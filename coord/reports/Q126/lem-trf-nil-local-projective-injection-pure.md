## Worker report

The module `lean/Sheaf/SecTraceFormula/NilLocalProjectiveInjectionPure.lean` states
`LinearMap.injective_lTensor_of_projective_of_nil_maximalIdeal`.  It does not prove the
statement: the proof is `sorry`, as required for stage 2.  The source is Stacks Project,
More on Algebra, Tags 05GM, 05GN, 05GP, and 05GQ, implication (1) to (2), specialized to
a local ring whose maximal ideal consists of nilpotent elements.

The Lean rendering of each hypothesis and conclusion clause is:

* The commutative ring and local-ring hypotheses are `(A : Type u) [CommRing A]
  [IsLocalRing A]`.  The canonical unique maximal ideal is Mathlib's
  `IsLocalRing.maximalIdeal A`.
* “Every element of the maximal ideal is nilpotent” is
  `(hnil : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → IsNilpotent a)`.
* The arbitrary projective modules and their module structures are
  `(P : Type v) (Q : Type w) [AddCommGroup P] [AddCommGroup Q] [Module A P]
  [Module A Q] [Module.Projective A P] [Module.Projective A Q]`.  No finite-generation
  hypothesis is present.
* The map and its injectivity hypothesis are
  `(u : P →ₗ[A] Q) (hu : Function.Injective u)`.
* Universal injectivity is rendered as
  `∀ (T : Type t) [AddCommGroup T] [Module A T],
  Function.Injective (u.lTensor T)`.  Here `LinearMap.lTensor T u` is the map
  `T ⊗[A] P →ₗ[A] T ⊗[A] Q` sending `t ⊗ p` to `t ⊗ u p`; the independent universe
  `t` allows every module universe.
* The final residue-field clause is
  `Function.Injective (u.rTensor (A ⧸ IsLocalRing.maximalIdeal A))`, which is the map
  `P ⊗[A] (A / maximalIdeal A) →ₗ[A] Q ⊗[A] (A / maximalIdeal A)`.
  The full conclusion is the conjunction of the preceding two clauses.

The statement dependencies used are the Mathlib declarations `Module.Projective` from
`Mathlib.Algebra.Module.Projective` and `TensorProduct` (notation `M ⊗[R] N`) from
`Mathlib.LinearAlgebra.TensorProduct.Defs`; the maps `LinearMap.lTensor` and
`LinearMap.rTensor` are from `Mathlib.LinearAlgebra.TensorProduct.Map`.  The proof plan
also imports the landed dependency module `Sheaf.RingTheory.ProjectiveOverLocalFree`,
whose declaration is `Module.free_of_projective_of_isLocalRing`; the free-module notion
is Mathlib's `Module.Free`, and the local-unit criterion used in the proof plan is
Mathlib's `IsLocalRing.notMem_maximalIdeal`.

The proof docstring records the source route: projective modules over a local ring are
free; a finite-free-source injection into a free target splits by induction using a unit
coefficient and the nilpotent common-annihilator argument; every tensor element has finite
basis support, reducing to a finite source; and tensor-factor symmetry gives the residue
field clause.  No proof data is introduced in the declaration.

Edge cases checked against the statement and proof route were: a field (maximal ideal
zero, including the zero-element case), the dual-number ring `k[ε]/(ε²)`, the zero
projective module and rank-zero finite source, arbitrary infinite-rank free modules, an
empty basis/index set, and the residue-field quotient itself.  The finite list in the
common-annihilator argument may be empty, where the witness is `1`; no nilpotence of the
whole maximal ideal or finite-generation assumption is added.

Searches made before writing the module:

* `msearch.py ... leanfinder "Over a commutative local ring with nilpotent maximal ideal, an injective map between arbitrary projective modules remains injective after tensoring with every module"`: returned local finite-module splitting criteria (`IsLocalRing.split_injective_iff_lTensor_residueField_injective`), flatness criteria, and localization results, all with extra finite/flat hypotheses; no match.
* `msearch.py ... loogle "LinearMap.lTensor, LinearMap.rTensor, Module.Projective, IsLocalRing"`: zero hits.
* `msearch.py ... grep "injective.*projective|projective.*injective|lTensor.*Injective|rTensor.*Injective" RingTheory`: hits only general flatness/localization lemmas and no theorem with this statement.
* `rg` over `WeilConjectures/` for nil-local/projective-injective/universally-injective patterns: only unrelated universal-injectivity and projective-line material.
* `rg` over `lean/Sheaf/` found generic universal-injectivity criteria (for example
  `LinearMap.universally_injective_tensor_iff`) and local-generic-basis results, but none
  states injective projective maps over nil local rings are pure.  Their finite or extra
  flatness hypotheses do not match this node.

The file compiled cleanly with:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q126 lem-trf-nil-local-projective-injection-pure lean/Sheaf/SecTraceFormula/NilLocalProjectiveInjectionPure.lean`

The node copy changes only its `lean` field and records the exact signature from the
module, with branch `newtargets-dag`, group `Q126`, and date `2026-10-19`.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
