# using AlgebraicTypeTheory

# #########
# # Tests #
# #########

# @doc """
# repeat the string y, x times
# """
# function fun(x::Int,y::String)::String
#     return y^x
# end

# f′ = mkFunc(fun)

# # Parse the symbol
# @test f′.sym == :fun


# # Parse the argument types and names
# @test f′.args == OrderedDict("x"=>Int, "y"=>String)

# # Determine the return type
# @test f′.return_type == String

# #A func whose return type does not match expected return type fails statically
# function badf(x::Int,y::String)::String return 2 end
# @test_throws AssertionError mkFunc(badf)

# # Parse the docstring --- CURRENTLY BROKEN
# @test f′.doc == "repeat the string y, x times"

# #Evaluate the serialized function with arguments
# @test funcEval(f′, [3, "abc"]) == "abcabcabc"

# #Evaluate the serialized function with keyword arguments
# @test funcEval(f′, Dict("y"=>"abc", "x"=>3)) == "abcabcabc"

# #This works for lambdas, too.
# fλ = mkFunc( (x::Int,y::String) -> y^x * string(x^x) )
# @test funcEval(fλ, Dict("y"=>"abc", "x"=>3)) == "abcabcabc27"

# #The JuliaFunction is actually a method, so we may need to discriminate which
# function fun(x::Int,y::Int)::Int return x*y  end
# f′′ = mkFunc(fun, [Int, Int]) # specify which method via types (otherwise the 1st)
# @test funcEval(f′′, Any[4,5]) == 20
