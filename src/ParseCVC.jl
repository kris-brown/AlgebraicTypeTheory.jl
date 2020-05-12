function parseCode(d::String)::Dict{String, String}
    m = eachmatch(r"% (\w+) => :(\w+)",d)
    return Dict([mm[1]=>mm[2] for mm in m])
end

function parseTerm(t::String)::String
    lets′ = eachmatch(r"(_let_\w+) = (.+?(?=\), _let|\) IN))", t)
    lets = Dict([m[1]=>m[2]*')' for m in lets′])
    inloc = findfirst("IN", t)
    startind = inloc === nothing ? 1 : inloc[2]+2
    term = t[startind:end]
    term_ = replace(reduce(replace, lets, init=reduce(
                replace, lets, init=term)), ", None"=>"")
    # convert free variables to distinct strings
    vars = eachmatch(r"(-\d+)", term_)
    varreplace = Dict([v[1]=>string("V",[Char(Int(x+48)) for x in v[1][2:end]]...)
                        for v in vars])
    term__ = reduce(replace, varreplace, init=term_)
    return term__
end

function remfirst(e::Symbol)::Union{Symbol,Expr} e end

function remfirst(e::Expr)::Union{Symbol,Expr}
    if length(e.args) == 3 return e.args[2]
    elseif length(e.args) > 3
        @assert e.args[1]==:ast
        args = map(remfirst,e.args[4:end])
        return Expr(e.head,e.args[2],args...)
    else throw(DomainError)
    end
end

function printTerm(t::String, d::String)::String
    code = parseCode(d)
    term = parseTerm(t)
    x = reduce(replace, sort(collect(code),rev=true,by=q->parse(Int,q[1])), init=term)
    x_ = string(remfirst(Meta.parse(x)))
    return x_
end


code = """% 1 => :Arr
% 2 => :Bool
% 3 => :Int
% 4 => :Ob
% 5 => :E
% 6 => :F
% 7 => :S
% 8 => :T
% 9 => :Z
% 10 => :ite
% 11 => :read
% 12 => :write
% 13 => :o
% 14 => :p
% 15 => :A"""

t = """LET _let_0 = ast(3, None, None, None, None), _let_1 = ast(7, _let_0, ast(9, _let_0, None, None, None), None, None), _let_2 = ast(4, None, None, None, None), _let_3 = ast(1, None, None, None, None), _let_4 = ast(2, None, None, None, None) IN ast(10, _let_2, ast(8, _let_4, None, None, None), ast(10, _let_2, ast(5, _let_4, ast(9, _let_0, None, None, None), _let_1, None), ast(13, _let_2, None, None, None), ast(11, _let_2, ast(12, _let_3, ast(15, _let_3, None, None, None), _let_1, ast(14, _let_2, None, None, None)), _let_1, None)), ast(-21, _let_2, None, None, None))"""

println(printTerm(t,code))
