## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SmoothSectionRegularImmersion.lean` states
`AlgebraicGeometry.smoothSection_regularImmersion`. It uses Mathlib's schemes and scheme
morphisms, `Smooth`, `IsImmersion`, `IsClosedImmersion`, `Spec`, `Spec.map`, open restriction,
and `RingTheory.Sequence.IsRegular`.

The theorem has the following rendering of the node statement.

* `{X S : Scheme.{u}}` introduces the two schemes of the node (`def-pc-scheme`).
* `(f : X ⟶ S) [Smooth f]` introduces the smooth morphism (`def-sbc-smooth-morphisms`), with
  no Noetherian, separatedness, quasi-compactness, or relative-dimension assumptions.
* `(s : S ⟶ X)` introduces the section morphism.
* `(hs : s ≫ f = 𝟙 S)` renders `f ∘ s = id_S`.
* The first conjunct `IsImmersion s` renders the global immersion conclusion
  (`def-weil-closed-immersion`).
* For every `t : S`, the second conjunct supplies an open `U : X.Opens` with
  `s t ∈ U`, rendering the neighbourhood of `s(t)`.
* `IsClosedImmersion (s ∣_ U)` renders the restricted map
  `s⁻¹(U) → U` as a closed immersion.
* The existential `A : CommRingCat.{u}`, `a : List A`, and isomorphisms
  `eU : U.toScheme ≅ Spec A` and
  `eZ : (s ⁻¹ᵁ U).toScheme ≅ Spec (.of (A ⧸ Ideal.ofList a))` render the affine descriptions
  `U = Spec A` and `s⁻¹(U) = Spec(A/(a_1,...,a_r))`.
* `RingTheory.Sequence.IsRegular A a` renders injectivity of multiplication by each list element
  on the successive quotients and nonzero final quotient, as in `def-weil-pbc-regular-sequence`.
* The final equality
  `eZ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList a))) =
  (s ∣_ U) ≫ eU.hom`
  identifies the quotient spectrum map with the actual restricted section over the affine chart.
  `List A` allows length zero, and the existential is under `∀ t`, so its length may vary with
  `t`; the empty scheme case is vacuous.

The proof is `sorry`, as required at stage 2. Its docstring records the five proof steps from the
node: immersion cancellation; affine closed-section reduction; smoothness of the two affine
algebras; the smooth-surjection regular-sequence theorem; and localization/quotient
identification.

Dependency declarations used:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
* `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
* `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; its immersion notion is
  `AlgebraicGeometry.IsImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
* `def-weil-pbc-regular-sequence`: `RingTheory.Sequence.IsRegular` in
  `Mathlib.RingTheory.Regular.RegularSequence`.
* The proof dependency `lem-pur-smooth-quotient-regular-sequence` is imported from
  `Sheaf.RingTheory.SmoothQuotientRegularSequence`, declaration
  `Algebra.exists_regularSequence_smooth_surjection`.
* The proof dependency `lem-pc-open-immersion-smooth-composition` is the Mathlib instances
  `AlgebraicGeometry.instSmoothOfIsOpenImmersion` and `AlgebraicGeometry.smooth_comp` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
* The proof dependency `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` is
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff` in
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`.
* The proof dependency `lem-zl-immersion-cancellation` is
  `AlgebraicGeometry.IsImmersion.of_comp` in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.

Edge cases checked against the statement and its definitions: the empty list is permitted by
`List A` and `Sequence.IsRegular` (Mathlib's `IsRegular.nil` applies for a nontrivial final
quotient); the list length is selected independently for each `t`; the identity section is the
zero-ideal/empty-list case; and when `S` is empty the pointwise clause is vacuous. No finiteness,
separation, or constant-dimension hypothesis was introduced.

Searches for an existing declaration were run on 2026-10-23/24:

* `msearch.py ... leanfinder "A section of a smooth morphism of schemes is an immersion locally defined by a finite regular sequence"`: hits were `IsSmooth`, standard-smooth chart and immersion declarations; no exact statement.
* `msearch.py ... leansearch "A section of a smooth morphism of schemes is a regular immersion"`: hits were `IsSmooth`, `IsImmersion`, `IsClosedImmersion`, and standard-smooth chart declarations; no exact statement.
* `msearch.py ... loogle '"IsSmooth", "IsImmersion"'`: one unrelated manifold immersion hit; no scheme statement.
* `msearch.py ... grep 'section.*regular.*immersion|regular.*immersion.*section|[Ss]mooth.*[Ss]ection' AlgebraicGeometry`: zero hits.
* Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for smooth-section/regular-immersion names found only the curve-specific Cartier theorem and unrelated regular-immersion infrastructure; no duplicate of this arbitrary-smooth-section statement.
* The Stacks source was read at `literature/stacks-project/divisors.tex`, Tag 067R,
  `lemma-section-smooth-regular-immersion`.

No new definition node or dependency repair was needed. No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
