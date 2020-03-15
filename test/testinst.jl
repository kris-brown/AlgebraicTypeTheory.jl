
using Test

using DataStructures: OrderedDict
using LinearAlgebra: I
using AlgebraicTypeTheory
using AlgebraicTypeTheory.Graph: viz
using AlgebraicTypeTheory.GraphTerm: App, Var, Sort
using AlgebraicTypeTheory.Inst: mkFunc, Instance,funcEval,JuliaType,instEval
using AlgebraicTypeTheory.Theories.Cat: cat
using AlgebraicTypeTheory.Theories.Monoid: monoid
using AlgebraicTypeTheory.Theories.Boolean: boolalg

##################
# JuliaFunctions #
##################

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
@test f′.args == OrderedDict(:x=>Int, :y=>String)

# Determine the return type
@test f′.return_type == String

# Parse the docstring
@test f′.doc == "repeat the string y, x times"

#Evaluate the serialized function with arguments
@test eval(funcEval(f′, [3, "abc"])) == "abcabcabc"

#Evaluate the serialized function with keyword arguments
@test eval(funcEval(f′, Dict(:y=>"abc", :x=>3))) == "abcabcabc"

# #The JuliaFunction is actually a method, so we may need to discriminate which
function fun(x::Int,y::Int)::Int return x*y  end
f′′ = mkFunc(fun, [Int, Int]) # specify which method via types (otherwise the 1st)
@test eval(funcEval(f′′, Any[4,5])) == 20

# Suppose we are in unknown environment, such that fun's meaning is uncertain
function fun(x::Int,y::Int)::Int nothing  end
@test eval(funcEval(f′′, Any[4,5])) == nothing
@test eval(funcEval(f′′, Any[4,5], false)) == 20 # use the source code, not relying on dispatch to resolve "fun"
#############
# Instances #
#############
function jint′()::Type Int end
jint = JuliaType(mkFunc(jint′))


struct MatrixDomain
  eltype::Type
  dim::Int
end
function md′()::Type MatrixDomain end
md = JuliaType(mkFunc(md′))
int2 = MatrixDomain(Int, 2)


function mkarray(mdl::MatrixDomain,mdr::MatrixDomain)::Type
    @assert mdl.eltype == mdr.eltype
    return Array{mdl.eltype, 2}
end

arr = JuliaType(mkFunc(mkarray))

function idmd(m::MatrixDomain)::Matrix
    Matrix{m.eltype}(I, m.dim, m.dim)
end
id = mkFunc(idmd)
@test eval(funcEval(id,Any[int2])) == [1 0; 0 1]

function onef()::Int 1 end
one = mkFunc(onef)
function intmul(q::Int,p::Int)::Int q*p end
mul = mkFunc(intmul)

icat = Instance(cat,Dict(:Ob=>md,:Hom=>arr),
             Dict(:id=>id,:mul=>mul))
imon = Instance(monoid, Dict(:Ob=>jint),Dict(:e=>one,:* => mul))



# this works
terms = [App(:*, [App(:e),App(:*, [Var(:y,Sort(:Ob)), Var(:x, Sort(:Ob))])]), App(:*, [App(:e),App(:*, [App(:e), App(:e)])]), App(:*, [Var(:x, Sort(:Ob)),App(:*, [Var(:x,Sort(:Ob)), App(:e)])])]

x,y = 3,4
@test [eval(instEval(imon,t)) for t in terms] == [12,1,9]

function landd(x::Set,y::Set)::Set intersect(x,y) end
function lorr(x::Set,y::Set)::Set union(x,y) end
function bott()::Set{Int} Set{Int}() end
function topp()::Set{Int} Set{Int}([1,2,3]) end
function negg(x::Set)::Set setdiff(Set([1,2,3]),x) end
land = mkFunc(landd)
lor = mkFunc(lorr)
bot = mkFunc(bott)
top = mkFunc(topp)
neg = mkFunc(negg)

# Boolean algebra on powerset of {1,2,3}
function ssi()::Type Set{Int} end
pset = JuliaType(mkFunc(ssi))

ibool = Instance(boolalg, Dict(:Bool=>pset),
    Dict(:∧ => land, :∨ =>lor, :⊤ => top, :⊥ =>bot, :¬ => neg))

bα, bβ = [Var(x, Sort(:Bool)) for x in [:α,:β]]

terms = [App(:∨, [App(:⊥), App(:¬, [App(:∨, [bα, bβ])])]),
         App(:∧, [App(:⊤), App(:¬, [App(:∨, [bα, bβ])])])]

α,β = Set([1]), Set([2])
@test [eval(instEval(ibool,t)) for t in terms] == [Set([3]),Set([3])]
