## Worker report

The module `Sheaf.RingTheory.BaseChangedAlgebraDifferentialGenerators` states
`Algebra.baseChanged_algebra_differential_generators`, with its proof `sorry`.
`KaehlerDifferential.ChosenGeneratorFormulas` is a transparent conjunction of
this node's differential clauses, not another construction of differentials.
Both declarations are listed in the node's `lean.declarations`. No statement,
proof plan, or dependency field has been changed; no additional nodes are needed.

Sources read: Stacks Project `algebra.tex`, Tag 0C4F,
`lemma-colimit-unramified`, its chosen-generator proof paragraph; Tag 00RX,
`lemma-differentials-polynomial-ring`, its first proof paragraph. The former
explicitly uses the chosen generators and their differentials before and after
scalar extension; the latter supplies the Leibniz induction used in the node.
The module docstring reproduces all five steps of the node's proof.

Hypothesis and conclusion correspondence:

- The four commutative rings are `A : Type u`, `B : Type v`, `C : Type w`,
  `T : Type z`, each with `[CommRing ...]`. Their universes are independent.
- The three given A-algebra structures are `[Algebra A B]`, `[Algebra A C]`,
  `[Algebra A T]`; the specified A-algebra map is `φ : B →ₐ[A] C`.
- `m : ℕ` allows every nonnegative integer. `x : Fin m → C` is the specified
  generating family, with indices shifted from 1,...,m to 0,...,m-1.
- Every element is a polynomial with coefficients acting through φ: `hx` is
  `Function.Surjective (MvPolynomial.eval₂Hom φ.toRingHom x)`. An arbitrary
  multivariate polynomial is a finite coefficient-weighted sum of monomials;
  conversely each finite expression in the node is such a polynomial.
- The tensor rings are literally `T ⊗[A] B` and `T ⊗[A] C`, with Mathlib's
  tensor ring multiplication. Their coefficient map is exactly
  `Algebra.TensorProduct.map (AlgHom.id A T) φ`; its `map_tmul` rule is
  `t ⊗ b ↦ t ⊗ φ b`. The chosen new generators are `(1 : T) ⊗ₜ[A] x r`.
- The first conjunct says the corresponding polynomial evaluation homomorphism
  over `T ⊗[A] B` is surjective, precisely algebra generation after base change.
- The second conjunct quantifies over every `t`, `c`, finite exponent set `s`,
  and coefficient family `b`. Its premise is the given expression for `c`,
  and its conclusion is the stated pure-tensor polynomial identity, with each
  `t ⊗ b e` acted on by the specified tensor map. In particular it does not
  replace this clause by an abstract finite-type assertion.
- The last two conjuncts apply `ChosenGeneratorFormulas` first to `φ.toRingHom`
  and `x`, and then to the actual tensor coefficient map and the tensor family.
  Inside this conjunction, `Submodule.span S (Set.range (fun r ↦ D ... (x r)))
  = ⊤` is the asserted spanning over the target algebra, in each case.
- The next clause in that definition quantifies over every coefficient `b : R`
  and exponent function `e : Fin m → ℕ`. `Finset.univ.filter (fun r ↦ 0 < e r)`
  implements exactly the positive-exponent summands. `(e r : S)` is the
  natural-number coefficient in S, `f b` is its base coefficient, the product
  over `Finset.univ.erase r` removes precisely the r-th factor, and
  `x r ^ (e r - 1)` supplies the remaining power. The resulting scalar acts
  on the actual universal differential `D ... (x r)`.
- The following clause explicitly asserts the additive extension for every
  finite polynomial expression: the differential of the finite sum equals
  the sum of those monomial derivatives, for each of the two algebras.
- The last clause is `m = 0 → Subsingleton (KaehlerDifferential R S)` with
  the ring-map-induced algebra argument written explicitly. This asserts that
  the actual differential module is zero for an empty generating family,
  separately before and after base change. These modules already contain zero,
  so Subsingleton has exactly the required meaning.

In the helper, every occurrence of `KaehlerDifferential.D` and the differential
module uses `f.toAlgebra` explicitly. Thus no arbitrary B-algebra structure on C,
or arbitrary algebra structure on the two tensor rings, is supplied as an extra
hypothesis. The helper is merely a reusable spelling of this item's clauses;
it introduces neither new mathematical data nor a new independent notion.
All variables and universes are explicitly bound; no file-local notation,
instance, private definition, `let`, or hidden `show ... from` is used.

Dependency declarations used and read:

- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation`. Read their definitions and
  docstrings, including the ambient ring/algebra binders. The statement uses
  the first two; the universal property explains their meaning. Mathlib's
  cotangent construction is the recorded differential object, so it is reused.
- `def-weil-pbc-module-tensor-product` is a Mathlib leaf, with no Lean record
  needed: `TensorProduct`, `TensorProduct.tmul`, `TensorProduct.lift`,
  `TensorProduct.ext'`, and `LinearMap.rTensor`, in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map`.
  Read the tensor type and pure-tensor declarations, the universal-property
  signature and uniqueness, and the recorded tensor-map interface. These are
  available through the public tensor-product imports. Ring multiplication
  and the specified coefficient map use
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`.

Edge cases checked mathematically before drafting:

- `m = 0`: polynomial evaluations consist of coefficients; the hypothesis is
  surjectivity of the base ring map, not an assertion excluding the case.
  All differential sums and spans are empty, and both modules vanish.
- Zero rings, a zero coefficient map in the unital zero-ring cases, and
  scalar extension to a zero ring are allowed by the types.
- `e r = 0` is omitted by the filter; no negative exponent is used. For
  `e r = 1` the remaining power is zero, as required.
- The zero polynomial is represented by an empty exponent set; both explicit
  sum formulas then give zero. Constant monomials have empty differential sum.
- Positive characteristic is retained: natural-number coefficients are cast
  into S, so derivatives of p-th powers vanish in characteristic p.
- No flatness, injectivity, nontriviality, or algebraic independence is assumed.
  The family can contain redundant or repeated elements.

Searches performed:

- `msearch.py`, LeanFinder: "A finite family generating an algebra still
  generates after simultaneous tensor base change and its differentials span
  the Kahler module". Eight results, including
  `Algebra.Generators.toKaehler_tmul_D`, cotangent-space representation lemmas,
  and `KaehlerDifferential.tensorKaehlerEquivBase`. These supply components,
  but none states all clauses for the given finite family and actual tensor map.
- `msearch.py`, Loogle: `KaehlerDifferential.span_range_derivation`.
  One result, that exact declaration. It spans by all differentials, rather
  than the differentials of the chosen generating family, and does not state
  the scalar-extension or polynomial formulas.
- `msearch.py`, grep in `RingTheory/Kaehler`:
  `span_range_derivation|baseChange_val|map_prod|map_pow`.
  Five results in `Kaehler/Basic.lean`, all referring to the all-differentials
  spanning theorem, not an exact match.
- Read local Mathlib tensor-map and multivariate-polynomial evaluation
  definitions after targeted `rg` searches; they provide the exact canonical
  constructions needed, so no construction has been duplicated.
- Searched `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `baseChanged.*[Gg]enerat|differential.*[Gg]enerat`. Found related modules,
  including `ColimitUnramifiedAlgebra`, whose proof uses this component, but
  no exact declaration. Searched both source trees and `dag/lean_names_upstream.json`
  for the two proposed full declaration names: no collision.

Validation: the required server `scompile.py` compiled both its sandbox view
and the final module view successfully (1.3 seconds each), with no errors or
unexpected warnings. The final delivery checks compile the exact final text.
No statement fault or dispute was found.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
