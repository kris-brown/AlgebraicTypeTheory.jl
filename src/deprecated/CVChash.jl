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
using LightGraphs: inneighbors

function allVars(t::Theory)::Dict{Symbol, Term}
    k = x -> getSig(x).premises
    return merge([k(s[2]) for s in t.sorts]...,
                 [k(o[2]) for o in t.ops]...,
                 [k(r) for r in t.rules]...)
end

"""Maximum depth required to apply rewrite rules."""
function maxdepth(r::Term)::Int
    g = r.g
    ds = Dict(root(g) => 0)
    md = 0
    for i in traverse(g, 0, false)
        if i != root(g)
            ds[i] = ds[inneighbors(g,i)[1]]+1
            if getkind(g, i) == VarNode && ds[i] > md
                md = ds[i]
            end
        end
    end
    return md
end


function maxdepth(t::Theory)::Int
    m = max([(maxdepth(getfield(r,f)),r,f)
                      for r in t.rules for f in [:t1, :t2]]...)
    println(m[1], m[2].name, m[3])
    return m[1]
end

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
        args = join([','*cvc(t,getarg(x, i), ctx) for i in 1:arity(x)])

        return "ast$(arity(x))($node$args)"
    end
end

"""A bijective mapping between natural numbers and sort/term ops"""
function symbolCode(t::Theory)::Dict{Symbol, Int}
    e = d -> enumerate(sort(collect(keys(d))))
    sd = Dict(e(t.sorts))
    od = Dict([(i+length(sd), v) for (i,v) in e(t.ops)])
    l = length(od)+length(sd)
    vd = Dict([(i+l,v) for (i,v) in e(allVars(t))])
    return Dict([(v, k) for (k,v) in collect(merge(sd, od, vd))]) # 0-index
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
        rterm = "\n\n% $srp -> $srt\nr$r$(dir)term: (T, INT) -> T = LAMBDA(x0: T, step: INT):\n\t$(cvc(t, term, ctx));\n\n"
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

function mkConcrete(t::Theory, cvals::Vector{Pair{String, Term}})::String
    res = ""
    repDict = Dict{String,String}()
    for (k, v) in cvals
        rawv = cvc(t, infer(t,v))
        vstr = reduce(replace, repDict, init=rawv)
        repDict[vstr] = k
        res *= "\n\n% $(render(t,v))\n$k: T = $vstr;"
    end
    return res
end

"""
Construct CVC4 file, optionally write to a path
"""
function writeFile(t::Theory, cvals::Vector{Pair{String, Term}}=Pair{String, Term}[],
                   pth::String="", extra::String="")::String
    symc = symbolCode(t)
    nodedict = Dict(v => k for (k, v) in symc)
    nsym = length(nodedict)
    tf = [true, false]
    arts = arities(t)
    mx = max(values(arts)...)
    nr = length(t.rules)
    nsrt = length(t.sorts)
    depth = maxdepth(t)
    paths = Iterators.flatten([Iterators.product(repeat([0:mx], d)...) for d in 1:depth])
    pathnames = ['P' * join(p) for p in paths]
    xs = ["x$(i-1)" for i in 1:(mx+1)]
    l = i -> string("ast$i : (INT, $(join(repeat(["T"],i),','))) -> T = ",
                    "LAMBDA (n: INT, $(join(xs[1:i],", ")): T):\n\tast(n,",
                    "mkHash$i(n,$(join(xs[1:i],", "))), ",
                    join(vcat(xs[1:i],repeat(["None"],mx-i+1)),", "), ");")

    a = i -> string("a$i: T -> T = LAMBDA (x: T): head(",
                    repeat("tail(",i),
                    "args(x$(repeat(')', i+2));")
    ga = i -> "ELSIF i = A$i THEN a$i(x)"
    len = i -> string(repeat("tail(",i), "l", repeat(')',i), "= nilA THEN $i")
    r = (i,d) -> "rule = R$i$d AND r$i$(d)pat(x) THEN r$i$(d)term(x, step)"
    getat = p -> "p = P$(join(p)) THEN a$(join(p,"(a"))(x$(join(repeat(')',length(p))))"
    hshij = (i,j) -> string(
        "mkHash$(j+1)(node(x),",
        join([i==k ? 'y' : "a$k(x)" for k in 0:j],", "),")")
    ri = i -> string(
        "replace$i : (T,T) -> T = LAMBDA (x,y: T):\n\t",
        "LET hsh = \n\t\tIF ",
        i==mx ? "FALSE THEN 0 " :
            join(["a$z(x)=None THEN "*hshij(i,z) for z in i+1:mx],"\n\t\tELSIF "),
        "\n\t\tELSE ",hshij(i,mx), "\n\t\tENDIF\n\tIN ast(node(x),hsh,",
        join([z == i ? 'y' : "a$z(x)" for z in 0:mx],","),");")

    """
    LET hsh = IF a2(x) = None THEN mkHash2(node(x), a0(x), y)
    ELSIF a3(x) = None THEN mkHash3(node(x), a0(x), y, a2(x))
    ELSE mkHash4(node(x), a0(x), y, a2(x), a3(x))
    ENDIF;
    IN
    ast(node(x),hsh,a0(x),y,a2(x),a3(x));
    """
    rat = p -> "p = P$(join(p)) THEN replaceP$(join(p))(x,y)"

    rw = i -> string("rewrite$i : T -> T = LAMBDA (x:T):\n\t",
                     join(repeat("rewrite(",i)),
                     "x,", join(["r$j,p$j, $j)" for j in 1:i],","),
                     ";")
    safeArg = i -> string(
        "A$i : T -> T = LAMBDA (x:T): ",
        "\n\tIF x = None THEN None ELSE a$i(x) ENDIF;")

    mh = i -> string("mkHash$i: (INT,$(join(repeat(['T'],i),','))) -> INT = LAMBDA(i:INT, $(join(xs[1:i],", ")): T): \n\t",
                     "pairZ$(i+1)(i, $(join(["hash($x)" for x in xs[1:i]],", ")));")

    # mkHash3: (INT,T,T,T) -> INT = LAMBDA(i:INT, x0,x1,x2: T): pairZ4(i, hash(x0),hash(x1),hash(x2))

    res = """% Generated with max arity $mx, max depth $depth

$(replace(render(t), "\n" => "\n% "))

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Meaning of nodes in A.S.T. % AUTO
%----------------------------------
% $(join(sort(nodedict), "\n% "))


% Datatypes
%----------


DATATYPE
    T = Error | None | ast (node: INT, hash: INT, $(join(["a$i: T" for i in 0:mx],", ")))
END;


DATATYPE % AUTO
    Path = Empty|$(join(pathnames, '|'))
END;

DATATYPE % AUTO
    Rule = $(join(["R$(i-1)f | R$(i-1)r" for i in 1:nr], " | "))
END;


% Hash functions

pairN2 : (INT, INT) -> INT = LAMBDA (x,y: INT):
    (((x+y)*(x+y+1) DIV 2) + 2) MOD 433494437;

pairN3 : (INT, INT, INT) -> INT = LAMBDA (x0,x1,x2: INT):
    pairN2(pairN2(x0,x1),x2);

pairN4 : (INT, INT, INT, INT) -> INT = LAMBDA (x0,x1,x2,x3: INT):
    pairN2(pairN2(x0,x1),pairN2(x2,x3));

pairN5 : (INT, INT, INT, INT, INT) -> INT = LAMBDA (x0,x1,x2,x3,x4: INT):
    pairN2(pairN2(x0,x1),pairN3(x2,x3,x4));

ZtoN : INT -> INT = LAMBDA(z:INT):
    IF z < 0 THEN 2*(-z)-1
    ELSE 2 * z
    ENDIF;

pairZ2 : (INT, INT) -> INT = LAMBDA (x,y: INT):
    pairN2(ZtoN(x), ZtoN(y));

pairZ3: (INT, INT, INT) -> INT = LAMBDA (x0,x1,x2: INT):
    pairN3(ZtoN(x0), ZtoN(x1), ZtoN(x2));

pairZ4: (INT, INT, INT, INT) -> INT = LAMBDA (x0,x1,x2,x3: INT):
    pairN4(ZtoN(x0), ZtoN(x1), ZtoN(x2), ZtoN(x3));

pairZ5: (INT, INT, INT, INT, INT) -> INT = LAMBDA (x0,x1,x2,x3,x4: INT):
    pairN5(ZtoN(x0), ZtoN(x1), ZtoN(x2), ZtoN(x3), ZtoN(x4));

$(join([mh(i) for i in 1:mx+1], "\n"))

% Convenience functions
%-----------------------

% Constructing ASTs % AUTO
ast0 : INT -> T = LAMBDA (n:INT):
	ast(n, n $(repeat(", None",mx+1)));
$(join([l(i) for i in 1:mx+1], "\n"))

% Access top-level argument of T % AUTO
$(join([safeArg(i) for i in 0:mx], '\n'))

% Replacing a top-level argument of an AST
$(join([ri(i) for i in 0:mx], "\n"))

% Replacing arbitrary element of an AST
$(join([replaceRec(p) for p in paths], '\n'))


mkVar : (INT, T) -> T = LAMBDA(v:INT,srt:T): ast1(v, srt);

% RULES

$(join([renderRule(t,i-1) for i in 1:nr],"\n"))

% Top level rewrite of a term
rewriteTop : (Rule, T, INT) -> T %AUTO
= LAMBDA(rule: Rule, x: T, step: INT):
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



rewrite : (T, Rule, Path, INT) -> T
    = LAMBDA (x: T, r: Rule, p: Path, step: INT):
       IF x = Error THEN Error
       ELSE
        LET presub = getAt(x,p)
        IN
            IF presub = Error THEN Error
            ELSE
                LET subbed = rewriteTop(r, presub, step)
                IN
                    IF (subbed = Error) THEN Error
                    ELSE replaceAt(p, x, subbed)
                    ENDIF
            ENDIF
       ENDIF;

r1,r2,r3,r4,r5,r6,r7: Rule;
p1,p2,p3,p4,p5,p6,p7: Path;
$(join([rw(i) for i in 1:7], "\n"))


% Concrete values
%-----------------
$(mkConcrete(t, cvals))


%------------
$extra
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