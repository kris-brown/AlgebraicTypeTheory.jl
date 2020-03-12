if isdefined(@__MODULE__, :LanguageServer)
    include("../src/AlgebraicTypeTheory.jl")
end

using Documenter
using Literate

const literate_dir = joinpath(@__DIR__, "literate")
const generated_dir = joinpath(@__DIR__, "src", "generated")

@info "Loading AlgebraicTypeTheory.jl"
using AlgebraicTypeTheory

@info "Building Literate.jl docs"
for (root, dirs, files) in walkdir(literate_dir)
    out_dir = joinpath(generated_dir, relpath(root, literate_dir))
    for file in files
        if last(splitext(file)) == ".jl"
            Literate.markdown(joinpath(root, file), out_dir;
        documenter = true, credit = false)
            Literate.notebook(joinpath(root, file), out_dir;
        execute = true, documenter = true, credit = false)
        end
    end
end

@info "Building Documenter.jl docs"
makedocs(
  modules     = [AlgebraicTypeTheory],
  format      = Documenter.HTML(),
  sitename    = "AlgebraicTypeTheory.jl",
  doctest     = false,
  pages       = Any[
    "AlgebraicTypeTheory.jl" => "index.md",
    "Theories" => Any[
      "generated/theories/monoid.md",
      "generated/theories/boolean.md",
      "generated/theories/preorder.md",
      "generated/theories/cat.md",
      "generated/theories/cwf.md",      ],

      "Core" => Any[
        "generated/core/core.md",
        "generated/core/inst.md",
      ],
#       "Experimental features" => Any[
#         "generated/programs/algebraic_nets.md",
#       ],
#     "Modules" => Any[
#       "apis/core.md",
#       "apis/doctrines.md",
#       "apis/wiring_diagrams.md",
#       "apis/graphics.md",
#       "apis/programs.md",
#     ]
  ]
)
#
# @info "Deploying docs"
# deploydocs(
#   target = "build",
#   repo   = "github.com/kris-brown/AlgebraicTypeTheory.jl.git",
#   branch = "gh-pages",
#   deps   = nothing,
#   make   = nothing
# )
