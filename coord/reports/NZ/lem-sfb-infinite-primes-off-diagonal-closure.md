## Worker report

The delivery states `AlgebraicGeometry.infinitePrimes_offDiagonalClosure` in
`Sheaf.AlgebraicGeometry.InfinitePrimesOffDiagonalClosure`, with proof `sorry`.
Its helper `AlgebraicGeometry.residueTensorMap` constructs the canonical ring map
in the node using real Mathlib maps; it has no postponed data or proof.
The node statement and all non-`lean` fields are unchanged.

Source read: `literature/stacks-project/decent-spaces.tex`, Tag 088I,
`lemma-infinite-number`, lines 3458–3498, together with the absolute-product
context of Tag 088J. The theorem docstring carries all five steps of the node's
accepted common-overfield proof, including the precise closure argument.

Hypothesis and clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`.
- A field: `(k : Type v) [Field k]`, with independent universe `v`.
- The sequence of prime ideals: `p : ℕ → Spec (CommRingCat.of A)`.
  The underlying type of this affine scheme is `PrimeSpectrum A`, so its points
  are exactly prime ideals, without an additional geometric-point choice.
  Source index `n ≥ 1` is reindexed by `n + 1`.
- Pairwise distinct: `hp : Function.Injective p`.
- The specified field embeddings: the arbitrary supplied instances
  `[∀ n : ℕ, Algebra k ((Spec (CommRingCat.of A)).residueField (p n))]`.
  An algebra structure is exactly its structural unital homomorphism here;
  a unital map between fields is injective. No algebraicity is imposed.
- The residue fields use the recorded `Scheme.residueField`, literally the
  quotient of the local ring by its maximal ideal. Mathlib's
  `Scheme.Spec.residueFieldIso` identifies this with `Ideal.ResidueField`,
  canonically the fraction field of the prime quotient. No new residue-field
  definition is introduced.
- The ambient affine scheme has underlying space `PrimeSpectrum (A ⊗[ℤ] A)`.
  This is the underlying space of the specified `Spec(A ⊗ℤ A)`, or equivalently
  the absolute affine fibre product. No topological product is substituted.
- The canonical residue maps `A → κ(p)` are
  `((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
  (Spec (CommRingCat.of A)).Γevaluation p).hom`.
  The first map identifies `A` with global sections and the second evaluates
  the section at the point and passes to the residue field.
- `residueTensorMap A k (p n) (p m)` applies the two canonical residue maps,
  followed by the left and right inclusions into `κ(p n) ⊗[k] κ(p m)`.
  `Algebra.TensorProduct.productMap` over `ℤ` multiplies these two images.
  On a pure tensor it is exactly `a ⊗ b ↦ residue_n(a) ⊗ residue_m(b)`.
- Each image in E is `Set.range (PrimeSpectrum.comap (residueTensorMap ...))`.
  Mathlib's `Spec.map` has exactly this underlying point map. The three unions
  `⋃ n, ⋃ m, ⋃ (_ : n ≠ m), ...` take precisely all off-diagonal images.
- `closure` is their Zariski closure in the ambient prime spectrum.
- The absolute diagonal image is the range of
  `PrimeSpectrum.comap (Algebra.TensorProduct.lmul' ℤ (S := A)).toRingHom`.
  `lmul'` sends `a ⊗ b` to `ab`, exactly the multiplication map of the node.
- The conclusion `(closure E ∩ Set.range ...).Nonempty` states precisely that
  the closure meets the diagonal image.
- There is no `Algebra k A` binder, scalar tower on A, finiteness, reducedness,
  or separation hypothesis.

Dependency declarations and source signatures/docstrings read:
`Field` (Mathlib.Algebra.Field.Defs);
`AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
`Scheme.Γevaluation`, and `Scheme.Spec.residueFieldIso`
(Mathlib.AlgebraicGeometry.ResidueField);
`AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.ΓSpecIso`
(Mathlib.AlgebraicGeometry.Scheme);
`CategoryTheory.Limits.pullback`, its projections and `pullback.lift`
(Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback).
The latter module is publicly imported as the recorded fibre-product dependency;
the displayed affine product is already represented by its tensor ring.
Construction APIs read: `Algebra.TensorProduct.includeLeftRingHom`,
`includeRight`, `productMap`, `lmul'`, and `RingHom.toIntAlgHom`.
The stated proof prerequisites are imported privately:
`Field.exists_family_common_extension`
(Sheaf.FieldTheory.FamilyCommonExtensionFields) and
`Ideal.nonempty_minimalPrimes`
(Mathlib.RingTheory.Ideal.MinimalPrime.Basic).
`lem-sfb-sequence-tensor-off-diagonal-kernel` currently has no Lean record;
it is a proof-only dependency and its future module import is left to landing
maintenance. It is not needed to type this statement or construct its map.

Edge cases checked before writing: an empty or finite sequence is not claimed;
ℕ is infinite and injectivity is the source's exact distinctness condition.
A zero ring or a ring with finitely many primes cannot satisfy that condition.
The ambient ring is not required to be a k-algebra, so embeddings that are
incompatible on A are retained. Arbitrary fields, including positive
characteristic and inseparable extensions, remain allowed. Residue fields are
nontrivial fields, and no assertion of reducedness of their tensor products is
used. Independent ring and field universes are retained. The diagonal is the
absolute diagonal even when k has positive transcendence degree over its prime
field. A finite set of primes was checked as a reason not to replace the infinite
index set by a nonempty one: finitely many off-diagonal closed points need not
accumulate on the diagonal.

Searches actually run with `msearch.py NZ lem-sfb-infinite-primes-off-diagonal-closure`:

- LeanFinder: “Infinitely many distinct prime ideals with residue fields over a
  common field force the closure of off diagonal tensor spectrum images to meet
  the absolute diagonal”. Eight hits, including tensor-product spectrum maps,
  inseparable base-change homeomorphisms, and residue-field fibre results;
  no exact statement or one-line specialization.
- LeanSearch: “The closure of off diagonal residue field tensor product spectra
  of infinitely many distinct prime ideals intersects the absolute diagonal.”
  Eight hits: tensor-product spectrum projections, residue-field fibres, product
  spectra, and elementary closure results; no exact accumulation theorem.
- Loogle: `"PrimeSpectrum", "closure"`. Six hits, including
  `PrimeSpectrum.closure_range_comap` and
  `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`; none supplies this
  infinite-family diagonal accumulation assertion.
- Mathlib grep, RingTheory: `infinite.*diagonal|offDiagonal.*closure|off_diagonal.*closure`.
  Zero hits.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `off.diagonal|infinite.*primes|lem-sfb-infinite-primes-off-diagonal-closure`:
  unrelated matrix/complex off-diagonal uses and arithmetic infinitude-of-primes
  uses only. A narrower search for `infinite.*[dD]iagonal|offDiagonal.*closure|off_diagonal.*closure`
  found only unrelated infinite complex diagonals and a group-scheme tangent map.
- Direct upstream item-id search: no hit.
- Proposed declaration names `infinitePrimes_offDiagonalClosure|residueTensorMap`
  searched in Mathlib algebraic geometry, project sources and
  `dag/lean_names_upstream.json`: no collision.

No statement dispute, dependency interface repair, new node, or statement correction.

## Second reading by NZ

This is the worker's final self-check, not a claim of an independent worker review;
the dispatched workflow assigns independent review to the maintainer.
I reread the node and module together. The key checks were that the structural
k-actions occur only on scheme residue fields, the target tensor is over ℤ,
all ordered pairs with unequal indices enter the union, the prime-spectrum
comaps are contravariant in the canonical ring maps, and the diagonal comes
from multiplication rather than equality in a topological product. Each clause
is accounted for above. No mathematical mismatch was found and no statement
field was changed. The helper's universal-product construction uses only real
data, and the only theorem is left as `sorry` as stage 2 requires.

Validation: prescribed `scompile.py` succeeded in both sandbox and library module
modes with no warnings or errors. The prescribed `deliver2.py --no-push` printed
OK: the delivery passes server preflight and compiles.
