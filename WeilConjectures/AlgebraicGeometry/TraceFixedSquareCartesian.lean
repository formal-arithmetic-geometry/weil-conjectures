/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFixedScheme

/-!
# The Cartesian fixed square of a cohomological correspondence

Source: Weil conjectures blueprint, main-20261015,
`sec-trace-formula/sk-d-corr/prop-trf-fixed-square-cartesian.md`
(blueprint: prop-trf-fixed-square-cartesian).

The fixed scheme is the pullback of the correspondence map along the diagonal.
The theorem records its universal Cartesian property, both leg identities, the
commutativity relation, and the finite-Tor exceptional inverse-image composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable {F : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime]
  {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {n : ℕ}
  {hl : l ≠ F.p} {X : Over (Spec (.of F.k))}
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  {K : (trfFiniteTorFixed l E n X.left).FullSubcategory}

namespace TrfCohomologicalCorrespondence

/-- The finite-Tor exceptional stage for `d`, with its explicit compactification.
Source: the exceptional inverse-image clause of `prop-trf-fixed-square-cartesian`
(blueprint: prop-trf-fixed-square-cartesian). -/
public noncomputable abbrev fixedProjectionStage
    (c : TrfCohomologicalCorrespondence F l E n hl X K)
    (h : HasCompactification c.fixedProjection) :=
  letI := h
  TrfExceptionalStage l E n c.fixedProjection

/-- The finite-Tor exceptional stage for `i_F`, with its explicit compactification.
Source: the exceptional inverse-image clause of `prop-trf-fixed-square-cartesian`
(blueprint: prop-trf-fixed-square-cartesian). -/
public noncomputable abbrev fixedInclusionStage
    (c : TrfCohomologicalCorrespondence F l E n hl X K)
    (h : HasCompactification c.fixedInclusion) :=
  letI := h
  TrfExceptionalStage l E n c.fixedInclusion

/-- The finite-Tor exceptional stage for `c₁`, with its explicit compactification.
Source: the exceptional inverse-image clause of `prop-trf-fixed-square-cartesian`
(blueprint: prop-trf-fixed-square-cartesian). -/
public noncomputable abbrev firstLegStage
    (c : TrfCohomologicalCorrespondence F l E n hl X K)
    (h : HasCompactification c.c₁.left) :=
  letI := h
  TrfExceptionalStage l E n c.c₁.left

/-- The canonical exceptional comparison for the fixed-square factorization.
The equality `fixedScheme_relations c |>.2.1` transports the `d`-stage to the
composite `i_F ≫ c₁`; the comparison is then exactly
`TrfExceptionalStage.composition i_F c₁ D₁ Dd`. Source: the exceptional
inverse-image clause of `prop-trf-fixed-square-cartesian` (blueprint:
prop-trf-fixed-square-cartesian). -/
public noncomputable def fixedExceptionalComposition
    (c : TrfCohomologicalCorrespondence F l E n hl X K)
    (hd : HasCompactification c.fixedProjection)
    (hi : HasCompactification c.fixedInclusion)
    (hc₁ : HasCompactification c.c₁.left)
    (qi : QuasiCompact c.fixedInclusion)
    (qc₁ : QuasiCompact c.c₁.left)
    (Dd : fixedProjectionStage c hd)
    (Di : fixedInclusionStage c hi)
    (D₁ : firstLegStage c hc₁) :
    TrfExceptionalStage.exceptional Dd ≅
      TrfExceptionalStage.exceptional D₁ ⋙ TrfExceptionalStage.exceptional Di := by
  letI := qi
  letI := qc₁
  let h := (fixedScheme_relations c).2.1
  let P (g : c.fixedScheme ⟶ X.left) : Type _ :=
    ∀ (hg : HasCompactification g), letI := hg
      ∀ Dg : TrfExceptionalStage l E n g,
        Dg.exceptional ≅ (D₁.exceptional ⋙ Di.exceptional)
  have base : P (c.fixedInclusion ≫ c.c₁.left) := by
    intro hg Dg
    letI := hg
    exact TrfExceptionalStage.composition Di c.c₁.left D₁ Dg
  have transported : P c.fixedProjection := h ▸ base
  exact transported hd Dd

/-- The fixed square is Cartesian, its two correspondence legs agree with the fixed
projection, and finite-Tor exceptional inverse image composes along the factorization
`d = i_F ≫ c₁`. Source: blueprint `prop-trf-fixed-square-cartesian`, sole statement
(blueprint: prop-trf-fixed-square-cartesian).

Proof steps: (1) the fixed-scheme pullback universal property gives `IsPullback` and
`c i_F = Δ d`; (2) postcomposition with the two product projections gives
`c₁ i_F = d = c₂ i_F`; (3) separated finite-type permanence gives the required
geometric properties of `i_F`, `c₁`, and `d`; (4) quasi-compactness and Nagata's
compactification theorem provide compactifications and finite-dimensional bounds;
(5) etale-origin and finite-Tor preservation put all exceptional functors on the
specified bounded full subcategories; (6) the compact-support compositor and the
three restricted adjunctions give the Hom-bijection comparison; (7) Yoneda constructs
the natural isomorphism and its inverse, with naturality in both variables. The
last clause quantifies the three `TrfExceptionalStage` data and records the
canonical comparison produced by `TrfExceptionalStage.composition`, transported
along `fixedScheme_relations`.
-/
theorem fixed_square_cartesian
    (c : TrfCohomologicalCorrespondence F l E n hl X K) :
    IsPullback c.fixedInclusion c.fixedProjection c.toProduct (pullback.diagonal X.hom) ∧
      c.fixedInclusion ≫ c.c₁.left = c.fixedProjection ∧
      c.fixedInclusion ≫ c.c₂.left = c.fixedProjection ∧
      c.fixedProjection ≫ pullback.diagonal X.hom = c.fixedInclusion ≫ c.toProduct ∧
      ∃ (hd : HasCompactification c.fixedProjection)
        (hi : HasCompactification c.fixedInclusion)
        (hc₁ : HasCompactification c.c₁.left)
        (qi : QuasiCompact c.fixedInclusion)
        (qc₁ : QuasiCompact c.c₁.left)
        (Dd : fixedProjectionStage c hd)
        (Di : fixedInclusionStage c hi)
        (D₁ : firstLegStage c hc₁),
        ∃ e : TrfExceptionalStage.exceptional Dd ≅
            TrfExceptionalStage.exceptional D₁ ⋙ TrfExceptionalStage.exceptional Di,
          e = fixedExceptionalComposition c hd hi hc₁ qi qc₁ Dd Di D₁ := by
  sorry

end TrfCohomologicalCorrespondence
end WeilConjectures
