/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!
# The trace of affine space is an isomorphism

Let `a : 𝔸ⁿ_k ⟶ Spec k` be affine space of dimension `r = #n` over a field `k`, `Λ` a finite
coefficient ring whose exponent is invertible on `k`, and `γ : Λ(r)[2r] ≅ Ra^! Λ` any Tate
orientation of `a`. The untwisted smooth trace `(Ra_! Λ)[2r] ⟶ Λ(-r)`
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`) is an isomorphism: the
isomorphism `RΓ_c(𝔸^r, Λ) ≅ Λ(-r)[-2r]` is the trace map for compactly supported cohomology.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_counit_affineSpace`: the
  counit `Ra_! Ra^! Λ ⟶ Λ` of `Ra_! ⊣ Ra^!` is an isomorphism, for `a : 𝔸ⁿ_S ⟶ S` over a
  Noetherian base `S`.
- `AlgebraicGeometry.Etale.TateOrientation.isIso_untwistedSmoothTrace_affineSpace`: the untwisted
  smooth trace `(Ra_! Λ)[2r] ⟶ Λ(-r)` of affine space over a field is an isomorphism.

## Implementation details

The counit is invertible for the coordinate tower `𝔸¹(𝔸¹(⋯ S))` with its ordered adjunction
(`AlgebraicGeometry.Etale.exists_affineSpaceTopTrace`), whose left adjoint is `R(-)_!`
(`AlgebraicGeometry.Etale.affineTraceUnboundedCompactComparison`); being invertible does not
depend on the presentation of the left adjoint (by conjugation of adjunctions), so it transfers
to the canonical adjunction `Ra_! ⊣ Ra^!`, and along the isomorphism of the tower with `𝔸ⁿ_S`.
The smooth trace is `Ra_!(γ)` followed by the counit, and the untwisted smooth trace is the
smooth trace up to the (invertible) projection map and the Tate twist identifications.

This is the étale, finite-coefficient form of the statement. The `ℚ̄_ℓ`-Weil isomorphism
`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_artinSchreierOf_linearFunction`
is only known to exist, so it is not identified with this trace map here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Adjunction

variable {C D : Type*} [Category C] [Category D] {L L' : C ⥤ D} {R R' : D ⥤ C}

/-- Being invertible for the counit of an adjunction at an object does not depend on the
presentation of the left adjoint. -/
private lemma isIso_counit_app_of_iso_left (adj : L ⊣ R) (adj' : L' ⊣ R') (φ : L ≅ L') (K : D)
    [hK : IsIso (adj.counit.app K)] : IsIso (adj'.counit.app K) := by
  have h := conjugateEquiv_counit adj' adj φ.hom K
  have : IsIso (φ.hom.app _ ≫ adj'.counit.app K) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left (φ.hom.app _) _

/-- Being invertible for the counit of an adjunction at an object only depends on the object up
to isomorphism. -/
private lemma isIso_counit_app_of_iso (adj : L ⊣ R) {K K' : D} (e : K ≅ K')
    [hK : IsIso (adj.counit.app K)] : IsIso (adj.counit.app K') := by
  have h : L.map (R.map e.hom) ≫ adj.counit.app K' = adj.counit.app K ≫ e.hom :=
    adj.counit.naturality e.hom
  have : IsIso (L.map (R.map e.hom) ≫ adj.counit.app K') := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (L.map (R.map e.hom)) _

end Adjunction

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The counit `Rp_! Rp^! Λ ⟶ Λ` of the coordinate-tower projection `p : 𝔸¹(⋯ 𝔸¹(S)) ⟶ S`
is an isomorphism. -/
theorem isIso_rightDerivedUpperShriekAdjunction_counit_affineTraceProjection (S : Scheme.{u})
    [IsNoetherian S] [HasInvertibleExponent Λ S] (d : ℕ) :
    IsIso ((rightDerivedUpperShriekAdjunction Λ (affineTraceProjection S d)).counit.app
      (𝟙_ (DerivedCategoryModule Λ S))) := by
  obtain ⟨N, hN, hΛ, hS⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  obtain ⟨t, D, -, h⟩ := exists_affineSpaceTopTrace N hN Λ hΛ
  obtain ⟨-, -, hiso, -⟩ := h S hS d
  have := isIso_counit_app_of_iso_left (affineTraceAdjunction Λ N hΛ t D S hS d)
    (rightDerivedUpperShriekAdjunction Λ (affineTraceProjection S d))
    (affineTraceUnboundedCompactComparison Λ S d) (ordinaryFiniteUnit Λ S) (hK := hiso)
  exact isIso_counit_app_of_iso _ (unitIsoSingleFunctorConstantSheaf Λ S).symm (hK := this)

/-- The counit `Ra_! Ra^! Λ ⟶ Λ` of `Ra_! ⊣ Ra^!` for affine space `a : 𝔸ⁿ_S ⟶ S` over a
Noetherian base is an isomorphism. -/
theorem isIso_rightDerivedUpperShriekAdjunction_counit_affineSpace (n : Type u) [Finite n]
    (S : Scheme.{u}) [IsNoetherian S] [HasInvertibleExponent Λ S] :
    IsIso ((rightDerivedUpperShriekAdjunction Λ (𝔸(n; S) ↘ S)).counit.app
      (𝟙_ (DerivedCategoryModule Λ S))) := by
  let := Fintype.ofFinite n
  let d := Fintype.card n
  let σ : ULift.{u} (Fin d) ≃ n := Equiv.ulift.trans (Fintype.equivFin n).symm
  let e : 𝔸(n; S) ⟶ affineTraceTower S d :=
    (AffineSpace.reindexIso S σ).hom ≫ (affineTraceAffineSpaceIso S d).inv
  have he : e ≫ affineTraceProjection S d = 𝔸(n; S) ↘ S := by
    have h : (affineTraceAffineSpaceIso S d).hom ≫ 𝔸(ULift.{u} (Fin d); S) ↘ S =
        affineTraceProjection S d := AffineSpace.homOfVector_over _ _
    rw [Category.assoc, ← h, Iso.inv_hom_id_assoc, AffineSpace.reindexIso_hom,
      AffineSpace.reindex_over]
  have := isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso Λ e
  have := isIso_rightDerivedUpperShriekAdjunction_counit_affineTraceProjection (Λ := Λ) S d
  let adj := (rightDerivedUpperShriekAdjunction Λ e).comp
    (rightDerivedUpperShriekAdjunction Λ (affineTraceProjection S d))
  have : IsIso (adj.counit.app (𝟙_ (DerivedCategoryModule Λ S))) := by
    rw [Adjunction.comp_counit_app]
    infer_instance
  exact isIso_counit_app_of_iso_left adj _
    (rightDerivedLowerShriekCompIsoOfEq Λ e (affineTraceProjection S d) _ he).symm _

namespace TateOrientation

variable [HasTateTwist Λ] {X Y : Scheme.{u}} {a : X ⟶ Y} [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- If the counit `Ra_! Ra^! Λ ⟶ Λ` is invertible, so is the untwisted smooth trace
`(Ra_! Λ)[2d] ⟶ Λ(-d)` of any Tate orientation `γ`. -/
theorem isIso_untwistedSmoothTrace_of_isIso_counit (γ : TateOrientation Λ a d)
    [IsIso ((rightDerivedUpperShriekAdjunction Λ a).counit.app
      (𝟙_ (DerivedCategoryModule Λ Y)))] :
    IsIso γ.untwistedSmoothTrace := by
  have := isIso_projectionMap_of_finite Λ a
  have : IsIso γ.smoothTrace := by
    rw [TateOrientation.smoothTrace, Etale.smoothTrace]
    infer_instance
  have : IsIso γ.twistedSmoothTrace := by
    rw [twistedSmoothTrace]
    infer_instance
  rw [untwistedSmoothTrace]
  infer_instance

end TateOrientation

/-- For affine space `a : 𝔸ⁿ_k ⟶ Spec k` of dimension `r = #n` over a field `k`, a finite
coefficient ring `Λ` with exponent invertible on `k` and any Tate orientation
`γ : Λ(r)[2r] ≅ Ra^! Λ`, the untwisted smooth trace `(Ra_! Λ)[2r] ⟶ Λ(-r)` is an isomorphism. -/
theorem TateOrientation.isIso_untwistedSmoothTrace_affineSpace [HasTateTwist Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] (n : Type u) [Fintype n]
    (γ : TateOrientation Λ (𝔸(n; Spec (.of k)) ↘ Spec (.of k)) (Fintype.card n)) :
    IsIso γ.untwistedSmoothTrace := by
  have : HasInvertibleExponent Λ 𝔸(n; Spec (.of k)) := .of_hom (𝔸(n; Spec (.of k)) ↘ Spec (.of k))
  have := isIso_rightDerivedUpperShriekAdjunction_counit_affineSpace (Λ := Λ) n
    (Spec (.of k))
  exact isIso_untwistedSmoothTrace_of_isIso_counit γ

end AlgebraicGeometry.Etale
