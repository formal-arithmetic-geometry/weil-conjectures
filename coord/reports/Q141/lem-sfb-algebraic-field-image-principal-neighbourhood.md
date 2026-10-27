## Worker report

The module `Sheaf.RingTheory.AlgebraicFieldImagePrincipalNeighbourhood` states
`PrimeSpectrum.exists_basicOpen_image_subset_of_integral_field_algebra`, with
`sorry` as its entire proof. No new definitions or additional nodes are needed.
Only the assigned node's `lean` field changes. Its source was read in
`literature/stacks-project/limits.tex`, the full statement and proof of Tag 0E21,
`lemma-ample-profinite-set-in-principal-affine`. The node is precisely its affine
specialization, with the trivial ample line bundle. Here "integral k-algebra"
means integral over k, not a domain: the source explicitly takes the colimit of
finite k-subalgebras.

Hypothesis and conclusion correspondence:

- A commutative ring R is `{R : Type u} [CommRing R]`.
- A field k is `{k : Type v} [Field k]`, using `def-weil-field`'s Mathlib match.
- A commutative k-algebra A is `{A : Type w} [CommRing A] [Algebra k A]`.
- Every element satisfies a monic polynomial over k is
  `(hA : ∀ a : A, IsIntegral k a)`. The definition `IsIntegral` unfolds to
  existence of a monic polynomial whose evaluation under `algebraMap k A`
  vanishes. This imposes neither a domain condition nor finite dimension.
- An arbitrary ring homomorphism is `(φ : R →+* A)`. It need not respect k,
  and R is not equipped with a k-algebra structure.
- The underlying map of `h = Spec(φ)` is `PrimeSpectrum.comap φ`, contraction
  of prime ideals. `def-weil-affine-spectrum` records `AlgebraicGeometry.Spec`
  and `AlgebraicGeometry.Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`, which
  is publicly imported. Their definitions were read, together with the map's
  implementation through `Spec.topMap` in `Mathlib.AlgebraicGeometry.Spec`:
  the underlying map is exactly prime-ideal contraction. The statement uses
  these underlying spaces and maps, since its conclusion is purely topological;
  no replacement notion of spectrum or scheme map is introduced. This also
  permits independent ring universes u and w.
- An open W in Spec R is `(W : TopologicalSpace.Opens (PrimeSpectrum R))`.
- Its containing the entire image is
  `hW : Set.range (PrimeSpectrum.comap φ) ⊆ (W : Set (PrimeSpectrum R))`.
- Existence of f is `∃ f : R`.
- The first inclusion is `Set.range (PrimeSpectrum.comap φ) ⊆
  (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))`.
- The second inclusion is `PrimeSpectrum.basicOpen f ≤ W`, the order on opens
  being inclusion. `basicOpen f` has carrier `{p | f ∉ p.asIdeal}`, exactly
  the node's D(f). Both inclusions are joined by `∧`.

Dependency declarations read and used:

- Statement dependency `def-weil-field`: `Field` in
  `Mathlib.Algebra.Field.Defs`, full class signature and docstring read.
- Statement dependency `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`
  and `AlgebraicGeometry.Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`,
  full definitions and docstrings read; their underlying spaces/maps are used
  in the topological formulation explained above.
- Mathlib `IsIntegral` in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`
  and `PrimeSpectrum.basicOpen` in `Mathlib.RingTheory.Spectrum.Prime.Topology`.
- Proof dependencies on basic opens and compactness:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_comap_range`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`,
  `PrimeSpectrum.iSup_basicOpen_eq_top_iff`, and
  `PrimeSpectrum.compactSpace` in `Mathlib.RingTheory.Spectrum.Prime.Topology`
  (available through the public spectrum import); `Ideal.span_singleton_eq_top`
  in `Mathlib.RingTheory.Ideal.Span`.
- Proof dependency `lem-sc-finite-generated-integral-subring`:
  `Algebra.finite_adjoin_of_finite_of_isIntegral` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` (plain proof import).
- Proof dependencies on Artinian rings and finite spectrum:
  `IsArtinianRing.of_finite` and `IsArtinianRing.setOfPred_isPrime_finite`
  in `Mathlib.RingTheory.Artinian.Module` (plain proof import).
- Proof dependency on prime avoidance: `Ideal.subset_union_prime` in
  `Mathlib.RingTheory.Ideal.Operations` (plain proof import).

The declaration docstring reproduces all five proof steps: the empty-spectrum
case and finite basic-open cover, the finite integral k-subalgebra, the integer
subring factorization, prime avoidance giving a unit, and verification of both
inclusions. Every proof-dependency node is named there.

Edge cases checked before writing:

- A may be the zero ring: its prime spectrum and image are empty, and f=0
  gives the empty basic open, contained even in W=empty. No `Nontrivial A`
  hypothesis or inferred domain structure was introduced.
- If R is the zero ring, any ring map to A forces A to be the zero ring, so
  this same empty-spectrum case applies.
- Nonreduced algebras, including dual numbers over k, are allowed; infinite
  integral algebras are also allowed. No finite type, dimension, or reducedness
  hypothesis occurs.
- W=top is allowed (f=1 works). W=empty is allowed exactly when the image is
  empty. The finite family in the proof may be empty; the docstring retains
  the node's separate empty-family case.
- k has arbitrary characteristic. All three universes are explicitly bound
  independently. There are no auto-bound variables.

Searches actually performed with the prescribed msearch wrapper:

- `leanfinder`: "The image of the spectrum of an algebra integral over a field
  has a principal open neighborhood contained in any given open neighborhood".
  Eight hits, including `Algebra.ZariskisMainProperty.of_isIntegral`,
  `Algebra.zariskisMainProperty_iff'`, and `PrimeSpectrum.basicOpen`.
  None states the required neighbourhood of an entire image for arbitrary φ.
- `leansearch`: "The image of Spec of an algebra integral over a field admits
  a principal open neighborhood contained in any open neighborhood".
  Eight hits, including `PrimeSpectrum.isClosedMap_comap_of_isIntegral`,
  localization-away embeddings and affine basic-open image lemmas. These concern
  an integral map R→A, a localization, or a chosen affine open, rather than
  the stated arbitrary map into an algebra integral over an unrelated field.
- `loogle`: `"IsIntegral", "basicOpen"`: zero hits.
- `grep` (Mathlib): `principal.*neighb|IsIntegral.*basicOpen|basicOpen.*IsIntegral`:
  zero hits.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for
  `principal.*[Nn]eighb|algebraic.*[Ff]ield.*[Ii]mage|` followed by the exact item id:
  unrelated pointwise principal-neighbourhood lemmas, no matching declaration
  and no exact item tag. The chosen declaration name is new.

No statement correction or disputed statement was needed. The prescribed
`scompile.py` checked the module successfully in both sandbox and library
positions (1.2 s and 1.3 s), with no errors or non-sorry warnings.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
