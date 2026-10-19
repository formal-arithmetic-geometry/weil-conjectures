## Worker report

The delivery adds `lean/Sheaf/SixFunctors/TraceFormula/FiniteEtaleMarkingSections.lean` and states
`AlgebraicGeometry.exists_finite_etale_marking_sections` with proof `sorry`.  The declaration
uses the Mathlib/source notions recorded by the item's dependencies: `IsProper`, `Flat`,
`LocallyOfFinitePresentation`, `IsIntegral`, `IsLocallyNoetherian`, `CompactSpace`,
`IsFinite`, `IsIntegralHom`, `Surjective`, `Scheme.Hom.fiberToSpecResidueField`,
`IsGenericPoint`, `GeometricallyIntegral`, `IsIntegralCurve`, `IsEffectiveCartierCenter`,
`Etale`, `Scheme.Hom.smoothLocus`, `pullback`, `IsClosedImmersion`, and finite scheme
coproducts.  No new definition node or dependency repair was needed.

The hypotheses render the node clause by clause as follows.

* The source family is `g : X ⟶ B`, with `[IsIntegral X]`, `[IsIntegral B]`,
  `[IsLocallyNoetherian X]`, `[CompactSpace X]`, `[IsLocallyNoetherian B]`, and
  `[CompactSpace B]`.  These are the integral and locally Noetherian plus quasi-compact
  parts of the two integral excellent Noetherian schemes.
* Excellence is stated directly with the dependency's ring predicate:
  `hX : ∀ U : X.Opens, IsAffineOpen U → IsExcellent Γ(X, U)` and the analogous `hB`.
  This is the affine-open scheme formulation of “excellent scheme” and avoids introducing
  a second scheme-excellence definition.
* `[IsProper g]`, `[Flat g]`, and `[LocallyOfFinitePresentation g]` render the three
  hypotheses on `g`.
* `η : B`, `hη : IsGenericPoint η Set.univ`,
  `[GeometricallyIntegral (g.fiberToSpecResidueField η)]`, and
  `[IsIntegralCurve (g.fiberToSpecResidueField η)]` render the generic-point,
  geometrically integral, curve generic-fibre clause.
* `D : Scheme`, `i : D ⟶ X`, `hi : IsEffectiveCartierCenter i`, and
  `hDV : ∀ d : D, i d ∈ g.smoothLocus` render the effective Cartier marking and its
  containment in the smooth locus.  `[IsProper (i ≫ g)]` and `[Etale (i ≫ g)]`
  render the proper étale map to the base.  The effective-Cartier predicate itself
  supplies the closed-immersion condition through its recorded declaration.

For the conclusion, `B₁` and `b : B₁ ⟶ B` are followed by integrality, affine-open
excellence, local Noetherianity, quasi-compactness, `IsFinite b`, `IsIntegralHom b`, and
`Surjective b`.  The second group uses the actual fibre product `pullback g b` and its two
projections.  It states integrality, affine-open excellence, local Noetherianity and
quasi-compactness of `X₁`, then `IsFinite (pullback.fst g b)` and surjectivity of `a`, and
properness, flatness and locally finite presentation of `g₁`.

The generic-fibre clause is the existential `η₁ : B₁` with generic point, geometric
integrality and `IsIntegralCurve` for `g₁`.  The geometric-fibre comparison is rendered
for every `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]` and every geometric point
`tbar : Spec (.of Ω) ⟶ B₁` by
`Nonempty (pullback (pullback.snd g b) tbar ≅ pullback g (tbar ≫ b))`.
Smoothness over the pulled-back smooth locus is the pointwise implication
`(pullback.fst g b) x ∈ g.smoothLocus → x ∈ (pullback.snd g b).smoothLocus`.

The marking conclusion is represented by an integer `n`, a family of sections
`s : ∀ j : Fin n, B₁ ⟶ pullback g b`, and an isomorphism
`e : (∐ fun _ : Fin n ↦ B₁) ≅ pullback i (pullback.fst g b)`.  Each `s j` is exactly the
corresponding coproduct summand followed by `e.hom` and the divisor projection; each is a
section of `g₁`; distinct section ranges are disjoint; each coproduct summand is a closed
immersion into the pulled-back divisor; every section lands in the pulled-back smooth
locus; and `IsEmpty D → n = 0` records the empty-marking edge case.  The isomorphism `e`
expresses that the pulled-back divisor is the disjoint union of precisely those closed
subschemes, including its scheme structure.

The module imports the recorded declaration modules for the statement dependencies:
`Sheaf.RingTheory.ExcellentRing`,
`WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`, and the
Mathlib morphism, fibre, limit, closed-immersion, underlying-map, and algebraically-closed
field modules needed by the rendered signature.  The proof dependencies remain in the
node's proof plan and are intentionally not restated as declarations in this statement
module.

Edge cases checked before writing the signature were: `D` empty (`IsEmpty D`, `n = 0` and
an empty finite coproduct), an already split marking, a base which is a field, a nonnormal
excellent base (normalization is only a conclusion), and both characteristic zero and
positive characteristic.  The geometric-fibre quantifier uses the same algebraically
closed field `Ω` on both sides of the comparison.  The generic curve is stated with the
source's integral-curve notion rather than the unrelated smooth-curve convention.

Searches made:

* `msearch.py ... leanfinder "finite etale marking splits into disjoint sections after
  finite alteration"`: eight hits, all finite étale algebra/idempotent or normalization
  APIs; no theorem for this family-and-marking statement.
* `msearch.py ... loogle "AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite,
  Scheme.Hom.fiber"`: zero hits (the query's `Scheme.Hom.fiber` identifier was unknown).
* `msearch.py ... grep "finite.etale.*split|etale.*section" Mathlib/AlgebraicGeometry`:
  zero hits.
* `rg` over `WeilConjectures` for finite étale, marking, and disjoint sections found
  finite étale fundamental-group, torsor, and algebra APIs, but no declaration of this
  result.  A direct search for `exists_finite_etale_marking_sections` found no existing
  project declaration.
* The existing DAG node `def-trf-effective-cartier-center` records the exact upstream
  `AlgebraicGeometry.IsEffectiveCartierCenter`; the existing `def-pc-curve` record points
  to `AlgebraicGeometry.IsIntegralCurve`.  These were reused rather than copied.

No `STATEMENT-DISPUTED` issue or node fault was found.  The stage-1 statement is retained;
there is no statement correction, no new node, and no dependency module.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-18)

The maintainer's reader made two changes to `FiniteEtaleMarkingSections.lean`:

1. (H3) Clause (ii) of the node compares the geometric fibre of `g₁` at `t̄` with the
   geometric fibre of `g` at `b ∘ t̄`. Both are schemes over `Ω`. The delivered
   `Nonempty (pullback (pullback.snd g b) tbar ≅ pullback g (tbar ≫ b))` only asked for an
   isomorphism of bare schemes, which is weaker. It now reads
   `∃ e : pullback (pullback.snd g b) tbar ≅ pullback g (tbar ≫ b),
   e.hom ≫ pullback.snd g (tbar ≫ b) = pullback.snd (pullback.snd g b) tbar`, which is an
   isomorphism over `Spec Ω`. The citer lem-trf-excellent-base-marked-semistable-curve
   needs this form, because it carries the fibre properties over `Ω` (smooth except at
   ordinary double points) from `f₁` to `f'`.
2. (H8) The declaration docstring now gives the node's ten proof steps one by one.
   Before, it was a one-paragraph summary, and that summary wrongly credited integrality
   of `X₁` to base change.

Both files compile clean with tools/nt_compile.py.
