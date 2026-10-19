## Worker report

The module `lean/Sheaf/SecTraceFormula/UniversallyExactFPSplit.lean` states
`Module.universally_exact_finitely_presented_quotient_split` for a commutative
ring `R`, modules `A`, `B`, `C`, linear maps `i : A →ₗ[R] B` and
`p : B →ₗ[R] C`, injectivity of `i`, surjectivity of `p`, and
`LinearMap.ker p = LinearMap.range i`. The typeclass
`[Module.FinitePresentation R C]` renders the finitely presented quotient
clause. The universal exactness hypothesis is rendered for every
`Q : Type (max u t)` with `[AddCommGroup Q] [Module R Q]`; its three conjuncts
are injectivity of `i.rTensor Q`, `Function.Exact (i.rTensor Q) (p.rTensor Q)`,
and surjectivity of `p.rTensor Q`. The conclusion is
`∃ r : B →ₗ[R] A, r.comp i = LinearMap.id`, exactly the required retraction.
The proof is intentionally `sorry` at stage 2.

The dependency declarations used are:

* `Module.FinitePresentation` from `Mathlib.Algebra.Module.FinitePresentation`,
  the recorded exact Mathlib declaration for `def-sc-finitely-presented-module`.
* `TensorProduct` and `LinearMap.rTensor` from Mathlib's tensor-product
  modules (the recorded `mathlib_match` for `def-weil-pbc-module-tensor-product`);
  `LinearMap.rTensor` supplies the maps appearing in the universal exactness
  clause.

I checked the edge cases represented by the binders: `Q` is unrestricted apart
from being an `R`-module (including the zero module and empty underlying data),
`A` and `B` have no finite-generation or flatness assumptions, `C` may be zero,
and no characteristic or nonzero assumption is introduced. The independent
universes for `A`, `B`, and `C` are retained, while the test-module universe is
`max u t` as in the neighboring universally-exact statements, so it contains
the ring universe and does not make the test family vacuous.

Searches made before writing the module:

* `msearch.py ... leanfinder "universally exact sequence finitely presented quotient splits module"`:
  hits included only splitting theorems that assume a splitting already
  (`Module.finitePresentation_of_split_exact`) and presentation lemmas; no match.
* `msearch.py ... loogle "Module.FinitePresentation, LinearMap.rTensor, Function.Exact"`:
  zero hits.
* `msearch.py ... grep "universally_exact_finitely_presented_quotient_split|universally exact.*finitely presented" Algebra/Module RingTheory/Flat`:
  zero hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` for the target name and
  the universally-exact finitely-presented splitting phrase: no existing
  declaration.
* The node search `grep -rl 'lem-trf-universally-exact-fp-split' dag/nodes`
  found only the target node itself; no duplicate definition node.

The source statement and proof were read in the target node: Stacks Project
`algebra.tex`, Tags 058K and 058L. No statement correction or new node was
needed.

## Second reading by Q21

I reread the target node and the completed Lean signature clause by clause.
`R` is a commutative ring; `A`, `B`, and `C` are independent modules; `i` and
`p` are the stated linear maps; `hi`, `hp`, and `hip` render injectivity,
surjectivity, and kernel=image. The finite-presentation hypothesis is exactly
`Module.FinitePresentation R C`. For every test module `Q`, the three required
exactness clauses appear as the three conjuncts on `i.rTensor Q` and
`p.rTensor Q`. The conclusion is precisely a linear retraction of `i`.
Compilation with `scompile.py` passed cleanly. I found no omitted hypothesis,
extra assumption, weakened clause, duplicate notion, or hollow definition.
