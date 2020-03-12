module Inst
export JuliaFunction, JuliaType, Instance, mkFunc, funcEval

using AutoHashEquals: @auto_hash_equals
using DataStructures: OrderedDict
using Test: @test, @test_throws
using CodeTransformation: addmethod!

if isdefined(@__MODULE__, :LanguageServer)
    include("../src/DataTypes.jl")
    using .DataTypes
else
    using .DataTypes
end


@auto_hash_equals struct JuliaFunction
    sym::Symbol
    args::OrderedDict{String,Type}
    return_type::Type
    impl::Core.CodeInfo
    doc::Union{String,Nothing}
end

"""
Wrap a Julia Type with a function which will enumerate values of that type (if
finite, otherwise sample the domain)
"""
@auto_hash_equals struct JuliaType{T}
    sym::Type
    finite::Bool
    enum::Function
end

"""
Map a theory's sorts -> Julia types and operators -> Julia functions.
"""
@auto_hash_equals struct Instance
    theory::Theory
    types::Dict{SortOp,JuliaType}
    funcs::Dict{TermOp,JuliaFunction}
end



"""
Inspect function and gather metadata. If argument types are not provided to
   distinguish which method, then the first one is arbitrarily selected.
"""
function mkFunc(f::Function)::JuliaFunction
    if length(methods(f)) > 1
        print("WARNING: Arbitrary method is selected")
    end
    return mkFunc(f, nothing)
end

function mkFunc(f::Function, argtypes::Union{Nothing,Vector{DataType}}
                )::JuliaFunction

    name = typeof(f).name.mt.name
    method = argtypes === nothing ? first(methods(f)) : which(f, argtypes)
    args_ = Base.arg_decl_parts(method)[2][2:end]
    args = OrderedDict{String,Type}(
            map(((a, b),)->(String(Symbol(a)), eval(Symbol(b))), args_))
    impl = Base.uncompressed_ast(method)
    rtype = Base.code_typed(f, [method.sig.parameters[2:end]...])[1].second
    @assert rtype != Union{} "Inconsistency between code and return type sig?\n$method"
   # println(methods(f)); println(string(@doc f))
    if string(name)[1] != '#'  # lambda
        doc = strip(string(eval(:(@doc AlgebraicTypeTheory.$(Symbol(f))))))
        if length(doc) > 23 && doc[1:23] == "No documentation found."
            doc = nothing
        end
    else doc = nothing end
    return JuliaFunction(name, args, rtype, impl, doc)
end

"""
Supply args to a function by keyword
"""
function funcEval(f::JuliaFunction, args::Vector{Any})::Any
    function tmp end
    addmethod!(Tuple{typeof(tmp),values(f.args)...}, f.impl)
    return eval(:($tmp($(args)...)))
    # return tmp(args...)
end

function funcEval(f::JuliaFunction, ctx::Dict{String,Any})::Any
    args = map(((sym, type),)->type(ctx[sym]), collect(f.args))
    return funcEval(f, args)
end
end