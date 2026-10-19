## Worker report

The module `Sheaf.SecTraceFormula.FlatMittagLefflerCriterion` states
`Module.flat_mittag_leffler_criterion`, with proof `sorry`. It is the flat
Mittag-Leffler criterion of Stacks Project, Algebra, Tag 059S
(`lemma-flat-ML-criterion`). No definition or dependency repair is needed.

The theorem renders every clause as follows:

- `R` is a commutative ring: `{R : Type u} [CommRing R]`.
- `M` is an `R`-module: `{M : Type v} [AddCommGroup M] [Module R M]`.
- `M` is flat: `[Module.Flat R M]`, the recorded Mathlib declaration for
  `def-weil-pbc-flat-ring-map`'s module notion.
- The left side is exactly the tensor-product Mittag-Leffler predicate
  `Module.IsMittagLeffler R M`, the recorded project declaration for
  `def-trf-mittag-leffler-module`.
- On the right, `F : Type w` has `[AddCommGroup F] [Module R F]`; the premise
  `∃ n : ℕ, Nonempty (F ≃ₗ[R] (Fin n → R))` says precisely that `F` is
  isomorphic to `R^n` for a finite integer `n ≥ 0`. `Fin 0 → R` handles
  `n = 0`.
- For every `x : TensorProduct R F M`, the least support is rendered by
  `∃ G₀ : Submodule R F`, followed by membership in
  `Set.range (LinearMap.rTensor M G₀.subtype)` and the clause that every
  supporting `G` contains `G₀`. The range is the image of the map induced by
  `G ↪ F`, and `LinearMap.rTensor M` is the canonical tensor map from the
  recorded tensor-product dependency.

Dependency declarations used:

- `Mathlib.RingTheory.Flat.Basic`, `Module.Flat` (the module flatness notion
  recorded by `def-weil-pbc-flat-ring-map`).
- `Sheaf.RingTheory.IsMittagLeffler`, `Module.IsMittagLeffler`.
- `Mathlib.LinearAlgebra.TensorProduct.Pi`, `TensorProduct`; and
  `LinearMap.rTensor` (the tensor-product notion recorded by
  `def-weil-pbc-module-tensor-product`).

Edge cases checked: `n = 0` is included (`Fin 0 → R` is the zero module); the
zero ring and zero module are allowed; `F` and `M` need not be nonzero; the
index type in the Mittag-Leffler definition may be empty or infinite; and no
finiteness, nonemptiness, or flatness hypothesis is imposed on `F` beyond the
finite-free isomorphism premise. Least means least under submodule inclusion,
not merely minimal, as expressed by `G₀ ≤ G` for every supporting `G`.

Searches made (2026-10-18):

- `msearch.py ... leanfinder "flat module is Mittag Leffler iff every tensor in a finite free module has a least supporting submodule"`: eight hits, chiefly `Module.Flat` criteria; no flat module Mittag-Leffler least-support criterion.
- `msearch.py ... loogle "Module.IsMittagLeffler, LinearMap.rTensor, least submodule"`: zero hits; `Module.IsMittagLeffler` is not in Mathlib.
- `msearch.py ... grep "Mittag|least.*submodule|smallest.*submodule" RingTheory`: three unrelated hits; no matching declaration.
- `rg` in the project and upstream source for `flat_mittag_leffler_criterion`, `least.*submodule`, and the item id: no existing declaration. The project’s `Module.IsMittagLeffler` definition was found and used rather than duplicated.

The prescribed `scompile.py` check compiled this module cleanly in sandbox and
library forms. No statement fault or `STATEMENT-DISPUTED` applies.

## Second reading by Q17

I reopened the node, Stacks Tag 059S, and the completed module. The reread
confirmed the commutative-ring, module, and flatness hypotheses; the biconditional
has the exact tensor-product ML predicate on the left; the right quantifies all
modules isomorphic to finite free `R^n`, all tensors `x`, and identifies the
least supporting submodule by both support membership and the universal
inclusion clause. The tensor image uses `LinearMap.rTensor M G.subtype`, so the
map is induced by the inclusion `G ↪ F` with the stated tensor factor. No
hypothesis or edge case changed during the second reading.

## Maintainer review fix (2026-10-18)

The delivered signature left two universes free, and some instantiations of
those free universes made the statement false.

- The index and test universes of `Module.IsMittagLeffler R M` were left free.
  When the index universe is below that of `R`, the predicate is weaker than
  Stacks' "every set". Example: let `R : Type 1` be a valuation ring whose value
  group has cofinality beyond `Type 0`, and let `K` be its fraction field. Then
  `K` is flat and passes the `Type 0`-indexed predicate, but the ideals
  supporting `1 ∈ R ⊗ K` have no least element. The forward implication was
  therefore false at that instantiation. The index universe is now `max u s`.
- The test module was `F : Type w` with `w` free. When `w` is below the universe
  of a large `R`, only `n = 0` occurs, the right side holds trivially, and the
  reverse implication would make every flat module Mittag-Leffler. `F` now lives
  in `Type (max u w)`.

Nothing is lost by these pins. The predicate passes from a larger index or test
universe to a smaller one by `ULift`. The finite-free condition is invariant
under transport along `F ≃ₗ Fin n → R`. The docstring now states the universe
choice and gives the node's six proof steps. The fixed module compiles clean
per file.
