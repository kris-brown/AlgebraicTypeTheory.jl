export JuliaFunction, JuliaType, Instance, mkFunc, funcEval

using AutoHashEquals: @auto_hash_equals
using DataStructures: OrderedDict
using Test: @test, @test_throws
using CodeTransformation: addmethod!

"""
Concrete structure capturing information about an executable function.
"""
@auto_hash_equals struct JuliaFunction
  sym :: Symbol
  args :: OrderedDict{String, Type}
  return_type :: Type
  impl :: Core.CodeInfo
  doc :: Union{String,Nothing}
end

"""
Wrap a Julia Type with a function which will enumerate values of that type (if
finite, otherwise sample the domain)
"""
@auto_hash_equals struct JuliaType{T}
    sym :: Type
    finite :: Bool
    enum :: Function
end

"""
Map a theory's sorts -> Julia types and operators -> Julia functions.
"""
@auto_hash_equals struct Instance
    theory :: Theory
    types :: Dict{SortOp,JuliaType}
    funcs :: Dict{TermOp, JuliaFunction}
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
   method = argtypes == nothing ? first(methods(f)) : which(f, argtypes)
   args_ = Base.arg_decl_parts(method)[2][2:end]
   args = OrderedDict{String,Type}(
            map(((a,b),)-> (String(Symbol(a)),eval(Symbol(b))),args_))
   impl = Base.uncompressed_ast(method)
   rtype = Base.code_typed(f,[method.sig.parameters[2:end]...])[1].second
   @assert rtype!=Union{} "Inconsistency between code and return type sig?\n$method"
   # println(methods(f)); println(string(@doc f))
   if string(name)[1] != '#'  # lambda
      doc = strip(string(eval(:(@doc AlgebraicTypeTheory.$(Symbol(f))))))
      if length(doc)>23 && doc[1:23] == "No documentation found."
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

function funcEval(f::JuliaFunction, ctx::Dict{String, Any})::Any
    args = map(((sym, type),)->type(ctx[sym]), collect(f.args))
    return funcEval(f, args)
end


#########
# Tests #
#########

@doc """
repeat the string y, x times
"""
function fun(x::Int,y::String)::String
    return y^x
end

f′ = mkFunc(fun)

# Parse the symbol
@test f′.sym == :fun


# Parse the argument types and names
@test f′.args == OrderedDict("x"=>Int, "y"=>String)

# Determine the return type
@test f′.return_type == String

#A func whose return type does not match expected return type fails statically
function badf(x::Int,y::String)::String return 2 end
@test_throws AssertionError mkFunc(badf)

# Parse the docstring --- CURRENTLY BROKEN
@test f′.doc == "repeat the string y, x times"

#Evaluate the serialized function with arguments
@test funcEval(f′, [3, "abc"]) == "abcabcabc"

#Evaluate the serialized function with keyword arguments
@test funcEval(f′, Dict("y"=>"abc", "x"=>3)) == "abcabcabc"

#This works for lambdas, too.
fλ = mkFunc( (x::Int,y::String) -> y^x * string(x^x) )
@test funcEval(fλ, Dict("y"=>"abc", "x"=>3)) == "abcabcabc27"

#The JuliaFunction is actually a method, so we may need to discriminate which
function fun(x::Int,y::Int)::Int return x*y  end
f′′ = mkFunc(fun, [Int, Int]) # specify which method via types (otherwise the 1st)
@test funcEval(f′′, Any[4,5]) == 20
