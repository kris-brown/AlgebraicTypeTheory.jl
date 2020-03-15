module Inst
export JuliaFunction, JuliaType, Instance, mkFunc, funcEval, instEval

using LightGraphs: vertices, neighbors, nv
using MetaGraphs: MetaDiGraph
using AutoHashEquals: @auto_hash_equals
using DataStructures: OrderedDict
using CodeTransformation: addmethod!
using CodeTracking: definition

using AlgebraicTypeTheory.GraphTerm
using AlgebraicTypeTheory.Graph
################################################################
@auto_hash_equals struct JuliaFunction
    sym::Symbol
    args::OrderedDict{Symbol,Type}
    return_type::Type
    impl::Expr
    doc::Union{String,Nothing}
end

"""
Optionally wrap a Julia Type with a function which will enumerate values of that type (if finite, otherwise sample the domain) so that axioms can be checked.
"""
@auto_hash_equals struct JuliaType
    sym::JuliaFunction
    finite::Bool
    enum::Union{Nothing,Function}
end

JuliaType(s::JuliaFunction,f::Bool=false)=JuliaType(s, f, nothing)
"""
Map a theory's sorts -> Julia types and operators -> Julia functions.
"""
@auto_hash_equals struct Instance
    theory::Theory
    types::Dict{Symbol,JuliaType}
    funcs::Dict{Symbol,JuliaFunction}
end


###############################################
"""
Inspect function and gather metadata. If argument types are not provided to
   distinguish which method, then the first one is arbitrarily selected.
"""
function mkFunc(f::Function, modul::Module=Main)::JuliaFunction
    if length(methods(f)) > 1
        print("WARNING: Arbitrary method is selected")
    end
    return mkFunc(f, nothing, Main)
end

function parse_type(modul::Module,x::Union{Symbol,Expr})::Any
    if x isa Symbol
        return getproperty(modul,x)
    else
        @assert x.head == :curly
        args = [parse_type(modul, a) for a in x.args[2:end]]
        return getproperty(modul,x.args[1]){args...}
    end
end

function mkFunc(f::Function,
                argtypes::Union{Nothing,Vector{DataType}}, modul::Module=Main
                )::JuliaFunction
    name = typeof(f).name.mt.name
    method = argtypes === nothing ? first(methods(f)) : which(f, argtypes)
    x = Meta.parse(definition(String,method)[1])
    @assert x.head == :function
    sig, impl = x.args
    @assert impl isa Expr
    if sig.head == :(::) # we have return type
        sig1, rtypex = sig.args
        rtype = parse_type(modul,rtypex)
    else
        sig1 = sig
        rtype = nothing
    end
    @assert sig1.head == :call
    @assert name == sig1.args[1]
    args = OrderedDict{Symbol,Type}()
    for a in sig1.args[2:end]
        @assert a.head == :(::)
        push!(args,a.args[1] => parse_type(modul,a.args[2]))
    end

    if string(name)[1] != '#'  # no docs for lambdas
        doc = strip(string(eval(:(@doc $(Symbol(modul)).$(Symbol(f))))))
        if length(doc) > 23 && doc[1:23] == "No documentation found."
            doc = nothing
        end
    else
        doc = nothing
    end
    return JuliaFunction(name, args, rtype, impl, doc)
end

###############################################
"""
Supply args to a function by keyword
"""
function funcEval(f::T, ctx::Dict{Symbol,Any})::Any where {T<:Union{JuliaFunction, JuliaType}}
    args = map(((sym, type),)->type(ctx[sym]), collect(f.args))
    return funcEval(f, args)
end

"""
Create an expression which can be evaluated in an environment where all the datatypes/functions involved are defined.
"""
# function funcEval(f::T, args::Vector{Any}
#                   )::Expr where {T<:Union{JuliaFunction, JuliaType}}
#     function tmp end
#     println("Eval $(f.sym) $args")
#     # addmethod!(Tuple{typeof(tmp),values(f.args)...}, f.impl)
#     addmethod!(Tuple{typeof(tmp),repeat([Any], length(f.args))...}, f.impl)
#     return Expr(:call, tmp, args...)
#     # if arg_expr return :($tmp(args...))
#     # else  return :($tmp($(args)...))
#     # end
# end

# function funcEval2(f::T, args::Vector{Any}
#     )::Expr where {T<:Union{JuliaFunction, JuliaType}}
# callexpr = Expr(:call,f.sym,[Symbol("x$i") for i in 1:length(args)]...)
# blockexpr = Expr(:block,codeExprs...)
# funexpr = Expr(:function, callexpr,blockexpr)
# println("Eval $(f.sym) $args")
# return Expr(:call, f.sym, args...)
# end

function funcEval(f::T, args::Vector{Any}
    )::Expr where {T<:Union{JuliaFunction, JuliaType}}
    # eval(f.impl)
    return Expr(:call, f.sym, args...)
end



###############################################
"""Return a Julia expression to be evaluated from a Term
eval(instEval(matrixCat, mkApp(:id, Var(z::{Int,2})))) -> [1 0;0 1]

For sortedTerm nodes, we *could* evaluate the sort too and typecheck the result, the way Julia checks the return type matches whenever it's specified.
"""
function instEval(i::Instance, tt::Term)::Union{Symbol,Expr}
    # println("hash t $(hash(tt))")
    res = instEval(i,tt.g)
    # println(join(res,"\n"))
    return res[root(tt.g)]
end

SDict = Dict{Int,Union{Symbol,Expr}}
function instEval(i::Instance,g::MetaDiGraph,n::Int=0,
                  res = SDict())::SDict
    n = n == 0 ? root(g) : n
    # println("insteval $n")
    sym, kind = getsym(g,n), getkind(g,n)
    if !haskey(res,n)
        if kind in [AppNode,SortNode]
            f = kind == AppNode ? i.funcs[sym] : i.types[sym].sym
            for m in neighbors(g,n)
                merge!(res,instEval(i, g, m, res))
            end
            arg_inds = [getarg(g,n,i) for i in 1:arity(g,n)]
            args = Any[res[a] for a in arg_inds]
            res[n] = funcEval(f, args)
        elseif kind == VarNode
            res[n] = sym
        else  throw(DomainError(kind))
        end
    end
    return res

end
end