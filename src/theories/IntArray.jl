
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
ZeZ = App(:E,[Zero,Zero])

# Symbol, number of arguments, result sort, argument sorts, name
sucOp = OpDecl(:S, 1, Int, [i], "Successor")
eqOp = OpDecl(:E, "({1}≡{2})", Bool, [i, j], "Boolean equality")
iteOp = OpDecl(:ite, 3, Ob, [b, o, p],  "If-then-else")
readOp = OpDecl(:read, 2, Ob, [A, i],  "Read array at position i")
writeOp = OpDecl(:write, 3, Arr, [A, i, o], "Write to array at position i")

row = Rule("Read over write",
           App(:read,[App(:write, [A, i, o]), j]),
           App(:ite, [App(:E, [i, j]), o, App(:read,[A, j])]))
eq2 = Rule("eq2", App(:E,[i,j]), App(:E,[App(:S,[i]), App(:S,[j])]))
eq1 = Rule("eq1", ZeZ, True)
eq3 = Rule("eq3", App(:E,[Zero,App(:S,[i])]), False)
eq4 = Rule("eq4", App(:E,[App(:S,[i]),Zero]), False)
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

default_examples = ["Zero" => Zero, "One" => One, "True"=>True, "ZeZ" => ZeZ,
                    "False" => False, "OeO" => App(:E, [One, One]),
                    "oObj" => o, "pObj" => p, "op" => op, "readop" => readop]

default_extra = """
QUERY rewrite1(ZeZ) /= True;
%QUERY rewrite7(readop) /= pObj;
COUNTERMODEL;

% 7 Step rewrite from readop to p
t1 :T = rewrite(readop, R0f, Empty, 1); % ite(E(Z, S(Z)), o, read(write(A, S(Z), p), S(Z)))
t2 :T = rewrite(t1, R3f, P1, 2); % ite(F, o, read(write(A, S(Z), p), S(Z)))
t3 :T = rewrite(t2, R6f, Empty,3); % read(write(A, S(Z), p), S(Z))
t4 :T = rewrite(t3, R0f, Empty,4); % ite(E(S(Z), S(Z)), p, read(A, S(Z)))
t5 :T = rewrite(t4, R2r, P1,5); % ite(E(Z, Z), p, read(A, S(Z)))
t6 :T = rewrite(t5, R1f, P1,6); % ite(T, p, read(A, S(Z)))
t7 :T = rewrite(t6, R5f, Empty,7); % p

"""

function writeCVC(examples=default_examples, extra=default_extra)::Nothing
    @assert haskey(ENV, "CVC4ROOT")
    writeFile(intarray_inferred, examples, ENV["CVC4ROOT"] * "/IntArray.cvc",
            extra, 4)
    return nothing
end


writeCVC()









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