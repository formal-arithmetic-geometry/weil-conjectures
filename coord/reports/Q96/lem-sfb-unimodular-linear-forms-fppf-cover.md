## Worker report

The module `Sheaf.AlgebraicGeometry.UnimodularLinearFormsFppfCover` states
`AlgebraicGeometry.unimodular_linear_forms_fppf_cover`, with its sole proof `sorry`.
Three concrete construction helpers in the same module name the polynomial product,
its localization, and the canonical spectrum morphism. They introduce no independent
notion: the polynomial is a finite product in Mathlib's `Polynomial R`, the algebra
is literally Mathlib's `Localization.Away`, and the morphism is literally `Spec.map`
of the composite of `Polynomial.C` with the localization's `algebraMap`. All four
names are listed in `lean.declarations`. No new node or dependency repair is needed.
The item's only changed field is `lean`.

Clause-by-clause correspondence with the unchanged node:

- An arbitrary commutative ring is `{R : Type u} [CommRing R]`; `u` is explicit.
  No domain, nonzero-ring, Noetherian, field, or characteristic assumption occurs.
- The natural number `n ≥ 0` is `{n : ℕ}`. The node's indices `1,…,n` are reindexed
  by `Fin n`; this includes the empty index set when `n = 0`.
- The elements `b_i,d_i` are `(b d : Fin n → R)`.
- Each pair generates the unit ideal by exactly the node's supplied criterion:
  `hunimodular : ∀ i, ∃ r s : R, r * b i + s * d i = 1`.
- The specified `P(Z)` is `unimodularLinearFormsPolynomial b d`, defined by
  `∏ i : Fin n, (Polynomial.C (b i) * Polynomial.X + Polynomial.C (d i))`.
  This is the product over all indices, and Mathlib's empty product is `1`.
- The specified ring `B` is `unimodularLinearFormsAlgebra b d`, an abbreviation for
  `Localization.Away (unimodularLinearFormsPolynomial b d)`. There is no arbitrary
  extension ring or map chosen in place of this localization.
- The specified `Spec B → Spec R` is `unimodularLinearFormsCover b d`. Its source
  and target are explicit `Spec (CommRingCat.of …)`; the defining homomorphism is
  `(algebraMap (Polynomial R) B).comp Polynomial.C`.
- Flatness is the first conjunct `Flat (unimodularLinearFormsCover b d)`.
- Surjectivity is the second conjunct `Surjective (unimodularLinearFormsCover b d)`.
- Local finite presentation is the third conjunct
  `LocallyOfFinitePresentation (unimodularLinearFormsCover b d)`.
- For `z`, the image of `Z`, the last conjunct states for each `i : Fin n` that
  `algebraMap (Polynomial R) B (Polynomial.C (b i) * Polynomial.X + Polynomial.C (d i))`
  is a unit. A ring map preserves sums and products, so this element is precisely
  the image of `b_i` times `z` plus the image of `d_i`. It is neither a unit
  assertion about some unrelated element nor an existential choice of `z`.
- The final sentence that this is a singleton fppf covering is exactly the three
  morphism properties just stated: the node defines an fppf covering to be a jointly
  surjective family of flat locally finitely presented morphisms. For a singleton,
  joint surjectivity is `Surjective`. No additional covering notion is substituted.

Statement dependencies, read at their recorded declarations and imported publicly:

| Node | Module | Declaration used |
| --- | --- | --- |
| def-weil-polynomial-ring | Mathlib.Algebra.Polynomial.Basic | `Polynomial`, with `Polynomial.C`, `Polynomial.X` |
| def-weil-ring-localization-away | Mathlib.GroupTheory.MonoidLocalization.Away (via Mathlib.RingTheory.Localization.Away.Basic) | `Localization.Away` and its ring `algebraMap` |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map` |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | `AlgebraicGeometry.Flat` |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | `AlgebraicGeometry.Surjective` |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | `AlgebraicGeometry.LocallyOfFinitePresentation` |

Proof-only dependencies are imported plainly, as the stage-3 proof plan:
`Mathlib.RingTheory.Flat.Basic` (`Module.Flat.of_projective`, `Module.Flat.of_free`),
`Mathlib.RingTheory.Flat.Localization` (`IsLocalization.flat`),
`Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat.comp`),
`Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial.instIsDomainOfIsCancelAdd`), and
`Mathlib.RingTheory.Spectrum.Prime.Topology`
(`PrimeSpectrum.localization_comap_isEmbedding`, `PrimeSpectrum.localization_comap_range`).
`AlgebraicGeometry.Flat.SpecMap_iff`, also a proof dependency, is provided by the public
flat-morphism import. Every proof dependency has a Mathlib match, so no proof import
is deferred. The theorem docstring carries the full proof plan, including the finite
presentation by `R[Z,T]/(TP-1)` and the prime-lifting surjectivity argument.

Sources opened: `literature/stacks-project/algebra.tex`, labels
`lemma-spec-localization` (Tag 00E3), `lemma-affineline-open` (00FB),
`lemma-composition-flat` (00HC), `lemma-ff-rings` (00HQ), and
`lemma-flat-localization` (00HT). These verify the elementary assembly in the node;
Conrad Proposition 4.3.1 is the node's application context rather than an additional
hypothesis. No source discrepancy or disputed statement was found.

Edge cases checked before drafting:

- `n = 0`: all pair hypotheses and unit assertions are vacuous, `P = 1`, and the
  localization is `R[Z][1/1]`. The spectrum morphism is the affine-line projection.
- The zero ring is allowed: its spectrum and the localization's spectrum are empty,
  so surjectivity is vacuous, while its sole element is a unit. There is no
  `[Nontrivial R]` restriction in any helper or theorem binder.
- A zero slope `b_i = 0` forces `d_i` to be a unit, so the constant linear factor
  causes no failure; a zero constant term forces the slope to be a unit.
- Finite residue fields do not require a scalar root-avoidance argument. The
  reduction of each factor is a nonzero polynomial in `(R/p)[Z]`; the product is
  nonzero even if it vanishes at every point of a finite residue field. The
  localization is a cover, without claiming a section over `R` or every residue field.
- Zero divisors and nilpotents are unrestricted. The construction uses localization
  at all powers of `P`, not a localization defined only for nonzero elements.

Searches run for this delivery (2026-10-24):

1. `msearch.py … leanfinder`: "A polynomial ring localized at the product of finitely
   many unimodular affine linear forms gives a flat surjective locally finitely
   presented spectrum map and makes the forms units". Eight hits, including
   `Algebra.SubmersivePresentation.localizationAway`,
   `Algebra.SubmersivePresentation.isStandardSmooth`, and
   `Algebra.IsStandardSmooth.finitePresentation`; none states this cover and all its clauses.
2. `msearch.py … loogle`: `Polynomial, Localization.Away, IsUnit`. Zero hits.
3. `msearch.py … leansearch`: "A polynomial ring localized at a product of unimodular
   affine linear forms has flat surjective locally finitely presented spectrum map".
   Eight hits, including `IsLocalization.flat`, `RingHom.Flat.holdsForLocalizationAway`,
   and `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. These are component
   results; none is the full node statement for the prescribed product and its factors.
4. `msearch.py … grep`: `Away.*[Ff]lat|[Ff]lat.*Away|unimodular`, subdirectory
   `RingTheory`: four hits in Flat/LocallyFree, Flat/Localization, and RingHom/Flat,
   with no simultaneous-unimodular-forms covering theorem.
5. `rg -n 'unimodular|linear.forms|linearForms|fppf_cover|fppfCover'` on both
   `lean/WeilConjectures` and `lean/Sheaf` found unrelated linear-form and fppf results.
   `grep -rn 'lem-sfb-unimodular-linear-forms-fppf-cover' lean/WeilConjectures`
   found no existing implementation.
6. A collision search for `unimodularLinearForms|unimodular_linear_forms` in Mathlib,
   both project Lean roots, and `dag/lean_names_upstream.json` found no existing names.

Validation: `scompile.py Q96 lem-sfb-unimodular-linear-forms-fppf-cover <module>` passed
both sandbox and library-name single-file checks (10.6 s and 5.7 s), with no errors or
unexpected warnings. All binders and the universe are explicit; `autoImplicit` is false.
The module's maximum line width is at most 100. The only postponed theorem is the
item itself, with its matching DAG node and source/proof docstring.

## Second reading by Q96

This is the author's second reading, not an independent review; the dispatcher brief
forbids starting another agent and assigns independent review to the maintainer.
I reopened the node and the written module and checked the ring, natural-number
indexing, unimodularity equation, product order, actual localization and direction of
the spectrum map. In particular, the map is induced by the composite `R → R[Z] → B`,
not the map `Spec B → Spec R[Z]` alone. The first three conjuncts use the recorded
scheme-morphism properties, and the final quantified unit is the image of each
specified linear polynomial, with the same index set as the hypothesis. The helper
abbreviation does not add a finite-presentation or flatness assumption. The source
ring can be trivial, and `Fin 0` is accepted. No mismatch was found and no statement
correction was needed.
