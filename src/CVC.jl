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

"""
Create CVC files that have a graph term structure.
"""

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
    return string(join(["A$i(" for i in reverse(v)]),
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
             ctx::Dict{String,Set{String}}=Dict{String,Set{String}}(),
             fv::Dict{Symbol,Int}=Dict{Symbol,Int}())::String
    if haskey(ctx,gethash(x))
        return first(ctx[gethash(x)])
    else
        s = getsym(x)
        node = getkind(x) == VarNode ? fv[s] : symbolCode(t)[s]
        args = join([','*cvc(t, getarg(x, i), ctx, fv) for i in 1:arity(x)])
        println("NEED TO MODIFY CVC() to do -10*step-node for Freevars")
        return "ast$(arity(x))($node$args)"
    end
end

"""A bijective mapping between natural numbers and sort/term ops"""
function symbolCode(t::Theory)::Dict{Symbol, Int}
    e = d -> enumerate(sort(collect(keys(d))))
    sd = Dict(e(t.sorts))
    od = Dict([(i+length(sd), v) for (i,v) in e(t.ops)])
    return Dict([(v, k) for (k,v) in collect(merge(sd, od))]) # 0-index
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
    sortcons = ["Node($(first(ctx[gethash(g,n)]))) = $(code[getsym(g,n)]) % $(getsym(g,n))"
                for n in traverse(g, 0, false) if getkind(g,n) in [SortedApp, SortNode]]
    eq = zs -> join(["$(first(zs))=$z" for z in zs[2:end]]," AND ")
    eqcons = [eq(collect(v)) for v in values(ctx) if length(v)>1]
    if isempty(eqcons)
        sortcons[end] = replace(sortcons[end], "%"=>"; %")
    end
    cons = vcat(sortcons,eqcons)
    return join(cons, "\n\tAND ")
end

function freevars(t1:: Term, t2::Term)::Dict{Symbol,Int}
    v1, v2 = [Set(keys(vars(x))) for x in [t1, t2]]
    fv = enumerate(sort(collect(setdiff(v2, v1))))
    return Dict([v=>-k for (k,v) in fv])

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
        freevar = freevars(pat, term)
        rterm = "\n\n% $srp -> $srt\nr$r$(dir)term: (T,INT) -> T = LAMBDA(x0: T, step: INT):\n\t$(cvc(t, term, ctx, freevar));\n\n"
        res = res * rpat * rterm
    end
    return res
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

function mkConcrete(t::Theory, cvals::Vector{Pair{String, Term}}, xtra::Dict{Symbol,Int})::String
    res = ""
    repDict = Dict{String,String}()

    for (k, v) in cvals
        rawv = cvc(t, infer(t,v), Dict{String,Set{String}}(), xtra)
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
                   pth::String="", extra::String="", depth::Int=0)::String
    symc = symbolCode(t)
    nsym = length(symbolCode(t))
    extravars = Dict([v=>k+nsym for (k,v) in enumerate(collect(union(
        [Set{Symbol}(keys(vars(x))) for (_, x) in cvals]...)))])

    nodedict = Dict(v => k for (k, v) in merge(symc, extravars))
    tf = [true, false]
    arts = arities(t)
    mx = max(values(arts)...)
    nr = length(t.rules)
    nsrt = length(t.sorts)
    depth = depth == 0 ? maxdepth(t) : depth
    paths = collect(Iterators.flatten([Iterators.product(repeat([0:mx], d)...) for d in 1:depth]))
    pathnames = ['P' * join(p) for p in paths]
    pathi = Dict([v=>k for (k,v) in enumerate(paths)])
    xs = ["x$(i-1)" for i in 1:(mx+1)]
    l = i -> string("ast$i : (INT, $(join(repeat(["T"],i),','))) -> T = ",
                    "LAMBDA (n: INT, $(join(xs[1:i],", ")): T):\n\tast(n,",
                    join(vcat(xs[1:i],repeat(["None"],mx-i+1)),", "), ");")

    len = i -> string(repeat("tail(",i), "l", repeat(')',i), "= nilA THEN $i")
    r = (i,d) -> "rule = R$i$d AND r$i$(d)pat(x) THEN r$i$(d)term(x, step)"
    getat = p -> "p = P$(join(p)) THEN a$(join(p,"(a"))(x$(join(repeat(')',length(p))))"

    rij = (i,j) -> string(
        "replace$(i)$(j) : (T,T) -> T = LAMBDA (x,y: T): ",
        "ast(node(x), l$j($(join([i==z ? 'y' : join(['a',z,"(x)"]) for z in 0:j-1],','))));")
    ri = i -> string("replace$i : (T,T) -> T = LAMBDA (x,y: T):\n\tIF    ",
                      join(["len(args(x)) = $z THEN replace$(i)$z(x,y)" for z in i+1:mx+1], "\n\tELSIF "),
                      "\n\tELSE Error % We covered every case\n\tENDIF;")
    rat = p -> "p = P$(join(p)) THEN replaceP$(join(p))(x,y)"

    rw = i -> string("rewrite$i : T -> T = LAMBDA (x0:T):\n\t",
                     join([string("LET x$j = rewrite(x$(j-1),r$j,p$j,$j) IN\n\tIF x$j = Error OR ",
                                  join(["x$j=x$k" for k in 0:j-1], " OR "),
                                  " THEN Error ELSE")
                            for j in 1:i],"\n\t"),
                     "\n\tx$i $(join(repeat("ENDIF ",i)));")

    ri = i -> string(
        "replace$i : (T,T) -> T = LAMBDA (x,y: T):ast(node(x),",
        join([z == i ? 'y' : "a$z(x)" for z in 0:mx],","),");")
    safeArg = i -> string(
        "A$i : T -> T = LAMBDA (x:T): ",
        "\n\tIF x = None THEN None ELSE a$i(x) ENDIF;")

    pn = p -> "ELSIF p = P$(join(p)) THEN -1$(join(p))"
    np = p -> string(
        "normalize$(join(p)) : T -> T = LAMBDA(x: T):\n\t",
        "LET n = getNAt(x,P$(join(p))) IN\n\t",
        "IF x = None THEN None\n\tELSIF n < 0 THEN\n\t\tIF ",
        join(["n=getNAt(x,P$(join(z))) THEN var(x,P$(join(z)))"
              for z in Iterators.take(paths, pathi[p]-1)], "\n\t\tELSIF "),
        "\n\t\tELSE var(x,P$(join(p)))\n\t\tENDIF\n\tELSE ",
        length(p) == depth - 1 ? 'x' : string("ast(node(x),",
        join(["normalize$(join(vcat(collect(p),i)))(A$i(x))" for i in 0:mx], ", "),')'),"\n\tENDIF;")
    res = """% Generated with max arity $mx, max depth $depth

$(replace(render(t), "\n" => "\n% "))

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Meaning of nodes in A.S.T. % AUTO
%----------------------------------
% $(join(sort(nodedict), "\n% "))


% Datatypes
%----------
DATATYPE
    T = Error | None | ast (node: INT, $(join(["a$i: T" for i in 0:mx],", ")))
END;

DATATYPE % AUTO
    Path = Empty|$(join(pathnames, '|'))
END;

DATATYPE % AUTO
    Rule = $(join(["R$(i-1)f | R$(i-1)r" for i in 1:nr], " | "))
END;

% Convenience functions
%-----------------------
% Constructing ASTs % AUTO
ast0 : INT -> T = LAMBDA (n:INT):
	ast(n$(repeat(", None",mx+1)));
$(join([l(i) for i in 1:mx+1], "\n"))

% Safe access to attributes of T % AUTO
Node : T -> INT = LAMBDA (x:T):
    IF x = None THEN 0 ELSE node(x) ENDIF;
$(join([safeArg(i) for i in 0:mx], '\n'))

% Replace top-level arg when we don't know how arity
$(join([ri(i) for i in 0:mx], "\n"))

% Replacing arbitrary element of an AST
$(join([replaceRec(p) for p in paths], '\n'))

%%%%%%%%%
% RULES %
%%%%%%%%%

$(join([renderRule(t,i-1) for i in 1:nr],"\n"))

%%%%%%%%%%%%%%%%%%%%%%%%
% PATHS INFRASTRUCTURE %
%%%%%%%%%%%%%%%%%%%%%%%%

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

pathNum : Path -> INT = LAMBDA(p:Path):
    IF p = Empty THEN -1
    $(join([pn(p) for p in paths],"\n\t"))
    ELSE 0 % impossible
    ENDIF;

%%%%%%%%%%%%%%%%%%%%%%%%%
% RENAME INFRASTRUCTURE %
%%%%%%%%%%%%%%%%%%%%%%%%%
% note: variables cannot be leaf nodes b/c their first arg is their sort.

getNAt : (T,Path) -> INT = LAMBDA (x:T, p:Path): Node(getAt(x,p));
var : (T,Path) -> T = LAMBDA(x:T,p:Path): ast(pathNum(p),a0(x));

% Normalize the wildcards introduced by rewrite rules

$(join(reverse([np(p) for p in paths if length(p) <= depth - 1][2:end]),"\n\n"))


normalize0 : T -> T = LAMBDA(x : T):
LET n = getNAt(x,P0) IN
    IF x = None THEN None
    ELSIF n < 0 THEN var(x, P0)
    ELSE ast(Node(x),normalize00(A0(x)),normalize01(A1(x)),normalize02(A2(x)))
    ENDIF;

normalize : T -> T = LAMBDA (x: T):
    IF x = None THEN None
    ELSIF Node(x) < 0 THEN var(x, Empty)
    ELSE ast(Node(x),normalize0(A0(x)),normalize1(A1(x)),normalize2(A2(x)))
    ENDIF;

%%%%%%%%%%%%%%%%%%%%%%%%%%
% REWRITE INFRASTRUCTURE %
%%%%%%%%%%%%%%%%%%%%%%%%%%


% Top level rewrite of a term
rewriteTop : (Rule, T, INT) -> T %AUTO
= LAMBDA(rule: Rule, x: T, step: INT):
    IF    $(join([r(i-1,d) for i in 1:nr for d in "fr"],"\n\tELSIF "))
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
$(mkConcrete(t, cvals, extravars))


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

