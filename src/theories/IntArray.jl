
if isdefined(@__MODULE__, :LanguageServer)
    include("../AlgebraicTypeTheory.jl")
    include("../GraphTerm.jl")
    include("../CVC.jl")
    using .GraphTerm
else
    using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render
    using AlgebraicTypeTheory.CVC: writeFile
end

sortnames = ["Ob", "Int", "Bool", "Arr"]
Ob, Int, Bool, Arr = [Sort(Symbol(x)) for x in sortnames]

o, p, b, A, i, j = [Var(x,y) for (x,y) in [(:o,Ob),(:p,Ob), (:b,Bool),(:A,Arr), (:i,Int), (:j, Int)]]

zeroOp = OpDecl(:Z,"0",Int,"Zero")
trueOp = OpDecl(:T,"⊤",Bool,"True")
falseOp = OpDecl(:F,"⊥",Bool,"Falsum")
Zero, True, False = [App(x) for x in [:Z, :T, :F]]

# Symbol, number of arguments, result sort, argument sorts, name
sucOp = OpDecl(:S, 1, Int, [i], "Successor")
eqOp = OpDecl(:≡, "binary", Bool, [i, j], "Boolean equality")
iteOp = OpDecl(:ite, 3, Ob, [b, o, p],  "If-then-else")
readOp = OpDecl(:read, 2, Ob, [A, i],  "Read array at position i")
writeOp = OpDecl(:write, 3, Arr, [A, i, o], "Write to array at position i")

row = Rule("Read over write",
           App(:read,[App(:write, [A, i, o]), j]),
           App(:ite, [App(:≡, [i, j]), o, App(:read,[A, j])]))
eq2 = Rule("eq2", App(:≡,[i,j]), App(:≡,[App(:S,[i]), App(:S,[j])]))
eq1 = Rule("eq1", App(:≡,[Zero,Zero]), True)
eq3 = Rule("eq3", App(:≡,[Zero,App(:S,[i])]), False)
eq4 = Rule("eq4", App(:≡,[App(:S,[i]),Zero]), False)
if1 = Rule("if1", App(:ite, [True,o,p]), o)
if2 = Rule("if2", App(:ite, [False,o,p]), p)

sorts = [SortDecl(Symbol(x)) for x in sortnames]
ops = [zeroOp, trueOp, falseOp, sucOp, eqOp, iteOp, readOp, writeOp]
rules = [row,eq1, eq2, eq3, eq4, if1, if2]
intarray = Theory(sorts, ops, rules, "IntArray", true)
intarray_inferred=Theory(sorts, ops, rules,"IntArray")

One = App(:S,[Zero])
op = App(:write, [App(:write,[A,One,p]), Zero, o])
readop = App(:read,[op, One])

default_examples = Dict("Zero" => Zero, "One" => One,
                        "oObj" => o, "pObj" => p, "op" => op, "readop" => readop,)

function writeCVC(depth=3, examples=default_examples)::Nothing
    @assert haskey(ENV, "CVC4ROOT")
    writeFile(intarray_inferred, examples, ENV["CVC4ROOT"] * "/IntArray.cvc", depth)
    return nothing
end
"""
t1 :T = rewrite(rewrite(rewrite(rewrite(rewrite(rewrite(rewrite(
				readop,		 % R(W(W(A,1,p),0,o),1)
				R0f, Empty), % Convert to ite(0=1, o, ...)
				R3f, P1),    % Convert 0=1 to ⊥
				R6f, Empty), % Convert ite(...) to R(W(A,1,p),1)
				R0f, Empty), % Convert to ite(1=1, p, R(A,1))
				R2r, P1),    % Convert 1=1 to 0=0
				R1f, P1),    % Convert 0=0 to ⊤
				R5f, Empty); % Convert ite(⊤,p,R(A,1)) to p
ASSERT t1 = pObj; % sat
"""

"""

####################################
# ******* Theory: IntArray ******* #
####################################

4 sorts, 8 ops, 7 rules

#########
# Sorts #
#########

==================================================

--------   Ob
Ob  sort


==================================================

---------   Arr
Arr  sort


==================================================

---------   Int
Int  sort


==================================================

----------   Bool
Bool  sort


##############
# Operations #
##############

==================================================
 A:Arr  i:Int
--------------   read
read(A,i) : Ob

Read array at position i


==================================================

-------   Z
0 : Int

Zero


==================================================
  i:Int
----------   S
S(i) : Int

Successor


==================================================
A:Arr  o:Ob  i:Int
------------------   write
write(A,i,o) : Arr

Write to array at position i


==================================================
b:Bool  o,p:Ob
---------------   ite
ite(b,o,p) : Ob

If-then-else


==================================================

--------   T
⊤ : Bool

True


==================================================
   i,j:Int
--------------   ≡
(i ≡ j) : Bool

Boolean equality


==================================================

--------   F
⊥ : Bool

Falsum


###################
# Equality Axioms #
###################

==================================================
                 A:Arr  o:Ob  i,j:Int
------------------------------------------------------   Read over write
read(write(A,i,o),j) = ite((i ≡ j),o,read(A,j))   : Ob


==================================================

--------------------------   eq1
(0() ≡ 0()) = ⊤()   : Bool


==================================================
            i,j:Int
--------------------------------   eq2
(i ≡ j) = (S(i) ≡ S(j))   : Bool


==================================================
           i:Int
---------------------------   eq3
(0() ≡ S(i)) = ⊥()   : Bool


==================================================
           i:Int
---------------------------   eq4
(S(i) ≡ 0()) = ⊥()   : Bool


==================================================
        o,p:Ob
-----------------------   if1
ite(⊤(),o,p) = o   : Ob


==================================================
        o,p:Ob
-----------------------   if2
ite(⊥(),o,p) = p   : Ob
"""