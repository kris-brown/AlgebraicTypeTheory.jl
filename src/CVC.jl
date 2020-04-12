module CVC
export
    cvc, writeFile


if isdefined(@__MODULE__, :LanguageServer)
    include("Graph.jl")
    include("GraphTerm.jl")
    using .Graph
    using .GraphTerm
else
    using AlgebraicTypeTheory.Graph
    using AlgebraicTypeTheory.GraphTerm
end

using DataStructures: DefaultDict
using Combinatorics: permutations

"""Represent the traversal of arguments from a term in CVC
E.g. the third argument of x's second argument: 'a3(a2(x))'
"""
function pth2cvc(arg::Int, v::Vector{Int})::String
    return string(join(["a$i(" for i in reverse(v)]),
                  "x$arg", repeat(')', length(v)))
end

"""Assuming the term is x_i in CVC, give a dictionary matching subterms in reference to the original x_i"""
function getCtx(arg::Int, t::Term)::Dict{String,Set{String}}
    g, h = t.g, gethash(t)
    res = DefaultDict{String, Set{String}}(()->Set{String}())
    seen = Set{Tuple{Int, Vector{Int}}}()
    todo = Tuple{Int,Vector{Int}}[(root(g), Int[])]
    while !isempty(todo)
        currnode, currpath = curr = pop!(todo)
        push!(seen, curr)
        push!(res[gethash(g, currnode)], pth2cvc(arg, currpath))
        # Only look at neighbors if this is the first time we've seen this node
        if length(res[gethash(g, currnode)]) == 1
            for i in 1:arity(g, currnode)
                new = (getarg(g,currnode,i), vcat(currpath, [i-1]))
                if !(new in seen)
                    push!(todo, new)
                end
            end
        end
    end
    return res
end

""""""
function getCtx(args::Vector{Term})::Dict{String,Set{String}}
    res = DefaultDict{String, Set{String}}(()->Set{String}())
    subsols = [getCtx(i-1,t) for (i,t) in enumerate(args)]
    for subsol in subsols
        for (k, v) in subsol
            union!(res[k], v)
        end
    end
    return res
end

"""Recursively convert a Term into a string in CVC language.
Relies on convenience constructor functions existing."""
function cvc(t::Theory, x::Term,
             ctx::Dict{String,Set{String}}=Dict{String,Set{String}}())::String
    if haskey(ctx,gethash(x))
        return first(ctx[gethash(x)])
    elseif getkind(x) == VarNode
        node = -parse(Int,gethash(x, true),base=16)
        srt = cvc(t,getarg(x, 1), ctx)
        return "mkVar($node, $srt)"
    else
        d = symbolCode(t)
        node = d[getsym(x)]
        args = join([cvc(t,getarg(x, i), ctx) for i in 1:arity(x)],", ")

        return "ast($node, l$(arity(x))($args))"
    end
end

"""A bijective mapping between natural numbers and sort/term ops"""
function symbolCode(t::Theory)::Dict{Symbol, Int}
    e = d -> enumerate(sort(collect(keys(d))))
    sd = Dict(e(t.sorts))
    od = Dict([(i+length(sd), v) for (i,v) in e(t.ops)])
    return Dict([(v, k-1) for (k,v) in collect(merge(sd, od))]) # 0-index
end

"""Sort or operation which has largest # of argument"""
function arities(t::Theory)::Dict{Symbol, Int}
    f = x -> Dict(k => length(v.args) for (k,v) in x)
    return merge(f(t.sorts), f(t.ops))
end

"""Given a rule pattern, get AND-joined constraints for the transition fn
This might be overkill, provided we want to assume that
any term that exists is well-typed.
"""
function renderPat(t::Theory, x::Term, ctx::Dict{String,Set{String}})::String
    code = symbolCode(t)
    g = x.g
    sortcons = ["node($(first(ctx[gethash(g,n)]))) = $(code[getsym(g,n)]) % $(getsym(g,n))"
                for n in traverse(g, 0, false) if getkind(g,n) in [SortedApp, SortNode]]
    eq = zs -> join(["$(first(zs))=$z" for z in zs[2:end]]," AND ")
    eqcons = [eq(collect(v)) for v in values(ctx) if length(v)>1]
    if isempty(eqcons)
        sortcons[end] = replace(sortcons[end], "%"=>"; %")
    end
    cons = vcat(sortcons,eqcons)
    return join(cons, "\n\tAND ")
end

"""Write part of the transition function"""
function renderRule(t::Theory, r::Int)::String
    rule = t.rules[r+1]

    it = [("f", rule.t1, rule.t2), ("r", rule.t2, rule.t1)]
    res = "% Rewrite rule $r\n%---------------\n"
    for (dir, pat, term) in it
        ctx = getCtx(0, pat)
        srp, srt = [render(t, x) for x in [pat, term]]
        rpat = "% $srp\nr$r$(dir)pat : T -> BOOLEAN = LAMBDA(x0: T):\n\t$(renderPat(t, pat, ctx));"
        rterm = "\n\n% $srp -> $srt\nr$r$(dir)term: T -> T = LAMBDA(x0: T):\n\t$(cvc(t, term, ctx));\n\n"
        res = res * rpat * rterm
    end
    return res
end

"""Convenience function for constructing a sort in CVC4"""
function sortConstructor(t::Theory, i::Int)::String
    sym = Dict(v => k for (k, v) in symbolCode(t))[i]
    decl = t.sorts[sym]
    if isempty(decl.args) return "mk$i : T = ast($i,nilA); %$sym"
    else
        n = length(decl.args)
        xs = ["x$(i-1)" for i in 1:(n)]
        return "mk$i : ($(join(repeat(['T'], n),", ")))->T = LAMBDA($(join(xs,", ")):T): ast($i, l$n($(join(xs,", ")))); %$sym"
    end
end

"""Convenience function for constructing a term operation in CVC4"""
function opConstructor(t::Theory, i::Int)::String
    sym = Dict(v => k for (k, v) in symbolCode(t))[i]
    decl = t.ops[sym]
    code = symbolCode(t) # Sym -> Int
    ctx = getCtx(decl.args)
    srt = cvc(t, decl.sort, ctx)
    if isempty(decl.args) return "mk$i : T = ast($i,l1($srt));"
    else
        n = length(decl.args)
        xs = ["x$(i-1)" for i in 1:(n)]
        return string("mk$i : ($(join(repeat(['T'], n),", ")))->T =",
                     "LAMBDA($(join(xs,", ")):T):\n\t",
                     "ast($i, l$(n+1)($srt,$(join(xs,", ")))); %$sym")
    end
end

"""A CVC function which replaces some subterm of x with y"""
function replaceRec(p)::String
    res = "replaceP$(join(p)) : (T, T) -> T = LAMBDA(x,y:T):\n\t"
    for i in 1:length(p)
        prev = ["a$z(" for z in reverse(p[1:i-1])]
        curr = p[i]
        res *= "replace$curr($(join(prev))x$(repeat(')',length(prev))),"
    end
    return res * "y$(repeat(')',length(p)));"
end

function mkConcrete(t::Theory, cvals::Dict{String, Term})::String
    res = ""
    repDict = Dict{String,String}()
    for (k, v) in cvals
        rawv = cvc(t, infer(t,v))
        vstr = reduce(replace, repDict, init=rawv)
        repDict[k] = vstr
        res *= "%$(render(t,v))\n$k: T = $vstr;"
    end
    return res
end
"""
Construct CVC4 file, optionally write to a path
"""
function writeFile(t::Theory, cvals::Dict{String, Term}=Dict{String, Term}(), pth::String="", depth::Int=6)::String
    symc = symbolCode(t)
    nodedict = Dict(v => k for (k, v) in symc)
    tf = [true, false]
    arts = arities(t)
    mx = max(values(arts)...)
    nr = length(t.rules)
    nsrt = length(t.sorts)
    paths = Iterators.flatten([Iterators.product(repeat([0:mx], d)...) for d in 1:depth])
    xs = ["x$(i-1)" for i in 1:(mx+1)]
    l = i -> string("l$i : ($(repeat("T,",i-1))T)",
                    "-> L[T] = LAMBDA ($(join(xs[1:i],", ")):T):",
                    "\n\tIF ($(join(["$x = Error" for x in xs[1:i]], " OR "))) THEN c(Error, nilA) \n\tELSE ",
                    " $(join(["c($x," for x in xs[1:i]]))",
                    " nilA$(repeat(')',i))\n\tENDIF;")

    a = i -> string("a$i: T -> T = LAMBDA (x: T): head(",
                    repeat("tail(",i),
                    "args(x$(repeat(')', i+2));")
    ga = i -> "ELSIF i = A$i THEN a$i(x)"
    len = i -> string(repeat("tail(",i), "l", repeat(')',i), "= nilA THEN $i")
    r = (i,d) -> "rule = R$i$d AND r$i$(d)pat(x) THEN r$i$(d)term(x)"
    getat = p -> "p = P$(join(p)) THEN a$(join(p,"(a"))(x$(join(repeat(')',length(p))))"

    rij = (i,j) -> string(
        "replace$(i)$(j) : (T,T) -> T = LAMBDA (x,y: T): ",
        "ast(node(x), l$j($(join([i==z ? 'y' : join(['a',z,"(x)"]) for z in 0:j-1],','))));")
    ri = i -> string("replace$i : (T,T) -> T = LAMBDA (x,y: T):\n\tIF    ",
                      join(["len(args(x)) = $z THEN replace$(i)$z(x,y)" for z in i+1:mx+1], "\n\tELSIF "),
                      "\n\tELSE Error % We covered every case\n\tENDIF;")
    rat = p -> "p = P$(join(p)) THEN replaceP$(join(p))(x,y)"
    res = """$(replace(render(t), "\n" => "\n% "))

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Meaning of nodes in A.S.T. % AUTO
%----------------------------------
% $(join(sort(nodedict), ", "))


% Datatypes
%----------
DATATYPE
  L[X] = n | c (head: X, tail: L[X])
END;

DATATYPE
    T = Error | ast_unsafe (node: INT, args: L[T])
END;

DATATYPE % AUTO
    Path = Empty|$(join(['P' * join(p) for p in paths], '|'))
END; % in ideal world with recursion... Path : TYPE = L[Arg];

DATATYPE % AUTO
    Rule = $(join(["R$(i-1)f | R$(i-1)r" for i in 1:nr], " | "))
END;

% Convenience functions
%-----------------------
% Empty lists
nilU : L[[INT, T]] = n::L[[INT, T]];
nilA : L[T] = n::L[T];

% Safe constructor % AUTO
ast: (INT, L[T]) -> T = LAMBDA( n: INT, a: L[T]):
    IF (n > $(max(values(symc)...))) OR ((a /= nilA) AND (head(a)=Error))
    THEN Error ELSE ast_unsafe(n,a) ENDIF;

% Length of AST lists
len : L[T] -> INT = LAMBDA (l:L[T]):
    IF l = nilA THEN 0
    ELSIF $(join([len(i) for i in 1:mx+1], "\n\tELSIF "))
    ELSE -1 % not possible
    ENDIF;

% Constructing argument lists % AUTO
$(join([l(i) for i in 1:mx+1], "\n"))

% Access top-level argument of T % AUTO
$(join([a(i) for i in 0:mx], "\n"))

% Replacing a top-level argument of an AST
$(join([rij(i,j) for j in 1:mx+1 for i in 0:j-1], "\n"))

% Replace top-level arg when we don't know how arity
$(join([ri(i) for i in 0:mx], "\n"))

% Replacing arbitrary element of an AST
$(join([replaceRec(p) for p in paths], '\n'))


mkVar : (INT, T) -> T = LAMBDA(v:INT,srt:T): ast(v, l1(srt));

% RULES

$(join([renderRule(t,i-1) for i in 1:nr],"\n"))

% Top level rewrite of a term
rewriteTop : (Rule, T) -> T %AUTO
= LAMBDA(rule: Rule, x: T):
    IF    $(join([r(i-1,d) for i in 1:nr for d in "fr"],"\n\tELSIF "))
    ELSE Error
    ENDIF;

getAt : (T, Path) -> T = LAMBDA(x:T, p:Path):
    IF    p = Empty THEN x
    ELSIF $(join([getat(p) for p in paths], "\n\tELSIF "))
    ELSE Error
    ENDIF;
replaceAt : (Path, T, T) -> T = LAMBDA(p:Path, x,y: T):
    IF    p = Empty THEN y
    ELSIF $(join([rat(p) for p in paths], "\n\tELSIF "))
    ELSE Error
    ENDIF;


rewrite : (T, Rule, Path) -> T
    = LAMBDA (x: T, r: Rule, p: Path):
       LET  presub = getAt(x,p),
            subbed = rewriteTop(r, presub)
       IN
       IF presub = subbed THEN Error % rewrite rules must change things
       ELSE  replaceAt(p, x, subbed)
       ENDIF ;


% Model specific convenient constructors %AUTO
$(join([sortConstructor(t,i-1) for i in 1:nsrt], "\n"))
$(join([opConstructor(t,i) for i in nsrt:nsrt+length(t.ops)-1], "\n"))

% Concrete values
%-----------------
$(mkConcrete(t, cvals))


%------------
t1,t2 : T;
test,test2,test3,test4,test5 : BOOLEAN;
ASSERT test = (t1=t2);

CHECKSAT TRUE;
COUNTERMODEL;

"""
    # All text replacements go in this list
    res = reduce(replace, ["l0()"=>"nilA"], init=res)

    if !isempty(pth)
        io = open(pth, "w"); write(io, res);  close(io);
    end

    return res
end
end

"""
%------------
t1,t2,t3,t4,t5 : T;
test,test2,test3,test4,test5 : BOOLEAN;
ASSERT t1 = pObj;

ASSERT t3 = rewrite(readop,R0f, Empty);

ASSERT t2 = rewrite(rewrite(rewrite(rewrite(rewrite(rewrite(rewrite(
				readop,
				R0f, Empty), % Convert to ite(0=1, o, ...)
				R3f, P1),    % Convert 0=1 to ⊥
				R6f, Empty), % Convert ite(...) to read(write(A,1,p),1)
				R0f, Empty), % Convert to ite(1=1, p, read(A,1))
				R2r, P1),    % Convert 1=1 to 0=0
				R1f, P1),    % Convert 0=0 to ⊤
				R5f, Empty); % Convert ite(⊤,p,read(A,1)) to p

ASSERT t4 = rewrite(t3, R3f, P1);

ASSERT t5 = rewriteTop(R3f, a1(t3));

ASSERT test = (t1=t2);
ASSERT test2 = (t2=t3);
ASSERT test3 = r3fpat(a1(t3));
ASSERT test4 = (t5 = a1(t3));
ASSERT test5 = (replace1(t3, t5) = t3);"""