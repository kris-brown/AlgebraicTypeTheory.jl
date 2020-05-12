if isdefined(@__MODULE__, :LanguageServer)
    include("../AlgebraicTypeTheory.jl")
    include("../GraphTerm.jl")
    include("../CVC.jl")
    using .GraphTerm
else
    using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render
    using AlgebraicTypeTheory.CVC: writeFile
end


Int, Bool = [Sort(Symbol(x)) for x in ["Int","Bool"]]
i, j  = [Var(x,y) for (x,y) in [(:i,Int), (:j, Int)]]
sucOp = OpDecl(:S, 1, Int, [i], "Successor")
eqOp = OpDecl(:E, "({1} ≡ {2})", Bool, [i, j], "Boolean equality")

zeroOp = OpDecl(:Z,"0",Int,"Zero")
trueOp = OpDecl(:T,"⊤",Bool,"True")
falseOp = OpDecl(:F,"⊥",Bool,"Falsum")
Zero, True, False = [App(x) for x in [:Z, :T, :F]]

eq2 = Rule("eq2", App(:E,[i,j]), App(:E,[App(:S,[i]), App(:S,[j])]))
eq1 = Rule("eq1", App(:E,[Zero,Zero]), True)
eq3 = Rule("eq3", App(:E,[Zero,App(:S,[i])]), False)
eq4 = Rule("eq4", App(:E,[App(:S,[i]),Zero]), False)

sorts = [SortDecl(Symbol(x)) for x in ["Int", "Bool"]]
ops = [zeroOp, trueOp, falseOp, sucOp, eqOp]
rules = [eq1, eq2, eq3, eq4]
One = App(:S,[Zero])

nat = Theory(sorts, ops, rules, "Nat", true)
nat_inferred=Theory(sorts, ops, rules,"Nat")
default_examples = ["Zero" => Zero, "One" => One, "True" => True,
                    "False" => False, "ZeqZ" => App(:E, [Zero, Zero]),
                    "OneEqOne" => App(:E, [One,One])]
default_extra = """
QUERY rewrite1(OneEqOne) /= ZeqZ; % possible: R1r @ []
COUNTERMODEL;
QUERY rewrite2(OneEqOne) /= ZeqZ; % but not possible in two steps
COUNTERMODEL;
QUERY rewrite2(OneEqOne) /= True; % possible: R1r @ [], R0f @ []
COUNTERMODEL;
QUERY rewrite2(OneEqOne) /= False; % not possible in two (or any) steps
COUNTERMODEL;
"""

function writeCVC(examples=default_examples, extra=default_extra)::Nothing
    writeFile(nat_inferred, examples, ENV["CVC4ROOT"] * "/Nat.cvc",
              extra)
    return nothing
end

writeCVC()
