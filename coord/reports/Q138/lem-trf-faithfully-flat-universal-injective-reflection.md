## Worker report

The module [FaithfullyFlatUniversalInjectiveReflection.lean](lean/Sheaf/TraceFormula/FaithfullyFlatUniversalInjectiveReflection.lean)
states `LinearMap.faithfullyFlat_universal_injective_iff`.

The ring hypotheses are `[CommRing R]`, `[CommRing S]`, and the canonical `R`-algebra
structure `[Algebra R S]`; `hS : (algebraMap R S).FaithfullyFlat` is the faithfully flat
ring-map hypothesis from `def-weil-pbc-faithfully-flat-ring-map`, expressed through the
canonical algebra map required by Mathlib's tensor constructions. `P` and `Q` are additive
commutative-group `R`-modules, and `u : P →ₗ[R] Q` is the given map. The universe
`Type (max u v w x t)` for both test-module quantifiers keeps the tests large enough for
the base rings and both source and target modules.

The left clause expands universal injectivity over `R`: for every
`L : Type (max u v w x t)` with `[AddCommGroup L] [Module R L]`,
`Function.Injective (u.lTensor L)` holds. Here `LinearMap.lTensor L u` is the map
`L ⊗[R] P → L ⊗[R] Q`, matching `L ⊗_R u` and the first-factor scalar action.

The right clause expands universal injectivity of the scalar extension over `S`: for every
`T : Type (max u v w x t)` with `[AddCommGroup T] [Module S T]`,
`Function.Injective ((LinearMap.baseChange S u).lTensor T)` holds. Mathlib's
`LinearMap.baseChange S u` is the canonical `S`-linear map
`S ⊗[R] P →ₗ[S] S ⊗[R] Q`, and `lTensor T` is the map
`T ⊗[S] (S ⊗[R] P) → T ⊗[S] (S ⊗[R] Q)`.

Dependencies used are the Mathlib declarations recorded by the node:

* `def-weil-pbc-faithfully-flat-ring-map`: `RingHom.FaithfullyFlat` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` (with
  `RingHom.faithfullyFlat_algebraMap_iff` for the canonical algebra-map presentation).
* `def-weil-pbc-module-tensor-product`: `TensorProduct` and its module structures in
  `Mathlib.LinearAlgebra.TensorProduct`; `LinearMap.lTensor` and
  `LinearMap.baseChange` are the induced maps used in the statement.

The proof dependencies in the node are reflected in the statement's intended route:
`TensorProduct.AlgebraTensorModule.cancelBaseChange` gives the forward cancellation
equivalence, `TensorProduct.AlgebraTensorModule.distribBaseChange` gives the reverse
distributivity equivalence, and `Module.FaithfullyFlat.lTensor_injective_iff_injective`
reflects injectivity after tensoring by `S`.

Edge cases checked: `P` or `Q` may be zero, `u` may be zero or the identity, and the test
module may be zero; the universal quantifiers and `Function.Injective` impose no
nontriviality assumptions. The universe bound uses `max u v w x t`, so tests are not
restricted below either ring or module universe. No existing project or Mathlib declaration
states this full equivalence; searches are recorded in `searches.jsonl` and included in the
node's `mathlib_searches`.

## Second reading by Q138

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
