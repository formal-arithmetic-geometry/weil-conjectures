/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.ModuleObjects.InternalScalarProjectionFormula
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization

/-! # Tor amplitude under restriction from a native regular quotient

Source: the principal resolution in the current blueprint integral Hom reduction.
(blueprint: lem-sf-condensed-regular-quotient-tor-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)

private theorem restricted_unit_tor :
    DerivedCategory.torAmplitudeIn _ (-1) 0
      ((Mod.comap (coefficientMap (reduction l E n) T)).mapDerivedCategory.obj
        (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (finite l E n) T))))) := by
  obtain ⟨_, _, _, _, _, hn⟩ :=
    (integral_quotient_resolution_normalization l E).2.2 T
  obtain ⟨_, _, hflat, _, _, _, ε, _, hε, _⟩ := hn n
  have := hε
  have : (resolution l E T n).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [resolution, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have : (resolution l E T n).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [resolution, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have hf (i : ℤ) : ObjectProperty.flat ((resolution l E T n).X i) := by
    have : PreservesFiniteLimits (tensorRight ((resolution l E T n).X i)) :=
      (hflat i).1
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight ((resolution l E T n).X i)).symm)
  let V : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (integral l E) T) :=
    Mod.comap (coefficientMap (reduction l E n) T)
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (integral l E) T)
  let B := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (finite l E n) T)
  let M : A := V.obj (Mod.regular (condensedRingObj (finite l E n) T))
  let e : DerivedCategory.Q.obj (resolution l E T n) ≅
      V.mapDerivedCategory.obj (𝟙_ (DerivedCategory B)) :=
    asIso (DerivedCategory.Q.map ε) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app M).symm ≪≫
      ((V.mapDerivedCategorySingleFunctor 0).app
        (Mod.regular (condensedRingObj (finite l E n) T))).symm ≪≫
      V.mapDerivedCategory.mapIso (DerivedCategory.singleFunctorObjUnitIso B)
  exact (DerivedCategory.torAmplitudeIn _ (-1) 0).prop_of_iso e
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0 hf)

/-- Restriction from O_E/pi^(n+1) to the pulled-back condensed O_E decreases the
lower endpoint of Tor amplitude by at most one and preserves the upper endpoint.
Source: latest blueprint lem-coef-integral-hom-reduction, principal resolution;
Stacks 06YY, 07A6 and 08FZ.
(blueprint: lem-sf-condensed-regular-quotient-tor-restriction).
Proof: the normalized two-term free resolution of the restricted regular
quotient lies in degrees -1 and 0. Its augmentation is a quasi-isomorphism, so
the restricted derived unit has Tor amplitude [-1,0]. The general projection
formula change-of-rings bound adds these endpoints to the Tor interval of K.
This argument includes the zero object, empty scheme and n = 0. -/
theorem torAmplitudeIn_restrict {a b : ℤ}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T))}
    (hK : DerivedCategory.torAmplitudeIn _ a b K) :
    DerivedCategory.torAmplitudeIn _ (a - 1) b ((restrict l E T n).obj K) := by
  have h := Mod.torAmplitudeIn_restriction_of_unit
    (coefficientMap (reduction l E n) T) hK (restricted_unit_tor l E T n)
  simpa only [sub_eq_add_neg, add_zero, restrict] using h

end AlgebraicGeometry.ProEtale.IntegralQuotient
