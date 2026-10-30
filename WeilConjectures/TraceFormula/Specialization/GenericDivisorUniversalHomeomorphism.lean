/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteCover
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteTransfer

/-!

# The constant case along a finite universal homeomorphism

Let `f : X' ⟶ X` be a finite universal homeomorphism of separated `k`-schemes of finite type,
`Z = V(I) ⊆ X` with complement `j : X ∖ Z ⟶ X`, and `j' : X' ∖ f⁻¹ Z ⟶ X'`. For a finite
discrete coefficient ring `T`, the restricted specialization `Le^* Ψ_X(j_! T̲)` vanishes near a
point `ζ` of `Z` as soon as `Le'^* Ψ_{X'}(j'_! T̲)` vanishes near every point of `f⁻¹ Z` over `ζ`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_of_isUniversalHomeomorphism`).

Indeed `Rf_* j'_! T̲ ≅ j_! Rv_* T̲` for the restriction `v : X' ∖ f⁻¹ Z ⟶ X ∖ Z`, and
`T̲ ⟶ Rv_* Lv^* T̲` is invertible by topological invariance, `v` being a universal homeomorphism;
the transfer of the vanishing along the finite morphism `f`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite`) concludes.

## Main results

- `ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism`:
  topological invariance for derived pullbacks of module objects.
- `ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_of_isUniversalHomeomorphism`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- **Topological invariance for derived pullbacks**: along a universal homeomorphism `r`, the
derived pullback `Lr^*` of module objects is an equivalence, so the unit of `Lr^* ⊣ Rr_*` is an
isomorphism. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    IsIso (derivedUpperStarLowerStarAdjunction Λ r).unit := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ r
  have : L((r)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (Functor.leftDerivedFunctorIsoMapDerivedCategory _).symm
  exact (derivedUpperStarLowerStarAdjunction Λ r).unit_isIso_of_L_fully_faithful

/-- **Pullback of the extension by zero of the unit**: let `g : X' ⟶ X`, `j : U ⟶ X` an open
immersion and `j' : U' ⟶ X'` a quasi-compact open immersion with closed complement `i'`, such that
`j' ≫ g` factors through `j` and `i' ≫ g` avoids `U`. Then `Lg^* j_! Λ ≅ j'_! Λ`: the restriction
of `Lg^* j_! Λ` to `Z'` vanishes, so it is `j'_! j'^* Lg^* j_! Λ`, and
`j'^* Lg^* j_! Λ ≅ Lv^* j^* j_! Λ ≅ Λ`. -/
theorem nonempty_leftDerivedUpperStar_openImmersionLowerShriek_unit_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X X' U U' Z' : Scheme.{u}} (g : X' ⟶ X) (j : U ⟶ X) [IsOpenImmersion j] (j' : U' ⟶ X')
    [IsOpenImmersion j'] [QuasiCompact j'] (v : U' ⟶ U) (hv : j' ≫ g = v ≫ j) (i' : Z' ⟶ X')
    [IsClosedImmersion i'] (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
    (hi' : Disjoint (Set.range j.base) (Set.range (i' ≫ g).base)) :
    Nonempty (L((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj (𝟙_ _)) ≅ D((j')_!open⟦Λ⟧).obj (𝟙_ _)) := by
  set A := L((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj (𝟙_ _))
  have hA : IsZero (L((i')^*⟦Λ⟧).obj A) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j (i' ≫ g) hi'
      _).of_iso ((leftDerivedUpperStarComp Λ i' g).app _)
  have := isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app Λ j' i' hij' A hA
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  let e : D((j')^*⟦Λ⟧).obj A ≅ 𝟙_ _ :=
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j').symm.app A ≪≫
      ((leftDerivedUpperStarComp Λ j' g).app _).symm ≪≫ eqToIso (by rw [hv]) ≪≫
      (leftDerivedUpperStarComp Λ v j).app _ ≪≫
      L((v)^*⟦Λ⟧).mapIso ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).app _ ≪≫
        (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app (𝟙_ _))).symm) ≪≫
      leftDerivedUpperStarUnitIso Λ v
  exact ⟨(asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').counit.app A)).symm ≪≫
    D((j')_!open⟦Λ⟧).mapIso e⟩

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The open complement of `V(f^* I)` is the inverse image of the complement of `V(I)`, so it is
the base change of the latter along `f`. -/
lemma isPullback_overRestrictι_compl_comap {k : Type u} [Field k] {X X' : Over (Spec (.of k))}
    (f : X' ⟶ X) (I : X.left.IdealSheafData) :
    IsPullback (overRestrictι X' (I.comap f.left).support.compl).left
      ((X'.left.isoOfEq (by ext1; simp [IdealSheafData.support_comap])).hom ≫
        f.left ∣_ I.support.compl)
      f.left (overRestrictι X I.support.compl).left :=
  (isPullback_morphismRestrict f.left I.support.compl).flip.of_iso
    (X'.left.isoOfEq (by ext1; simp [IdealSheafData.support_comap])).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {X X' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]

/-- **The constant case along a finite universal homeomorphism**: let `f : X' ⟶ X` be a finite
universal homeomorphism, `Z = V(I)`, `j : X ∖ Z ⟶ X` and `j' : X' ∖ f⁻¹ Z ⟶ X'`. If
`Le'^* Ψ_{X'}(j'_! T̲)` vanishes near every point of `f⁻¹ Z` over a point `ζ` of `Z`, then
`Le^* Ψ_X(j_! T̲)` vanishes near `ζ`: `Rf_* j'_! T̲ ≅ j_! Rv_* T̲ ≅ j_! T̲` by topological
invariance along the restriction `v` of `f`, and the vanishing transfers along the finite `f`. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_of_isUniversalHomeomorphism (f : X' ⟶ X)
    [IsFinite f.left] [IsUniversalHomeomorphism f.left] (I : X.left.IdealSheafData)
    (ζ : (centre X I).left)
    (h : ∀ ζ' : (centre X' (I.comap f.left)).left, (centreMap f I).left ζ' = ζ →
      nearbyCyclesVanishNear X' (I.comap f.left) k' (Profinite.continuousMapRingObj T) ζ'
        ((D(((overRestrictι X' (I.comap f.left).support.compl).left)_!open⟦
          Profinite.continuousMapRingObj T⟧)).obj (𝟙_ _))) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj T) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj T⟧)).obj (𝟙_ _)) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  set j' := (overRestrictι X' (I.comap f.left).support.compl).left
  set v := (X'.left.isoOfEq (by ext1; simp [IdealSheafData.support_comap])).hom ≫
    f.left ∣_ I.support.compl
  have hsq := isPullback_overRestrictι_compl_comap f I
  have : IsUniversalHomeomorphism v := by
    have : IsUniversalHomeomorphism (f.left ∣_ I.support.compl) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f.left I.support.compl).flip
        ‹_›
    dsimp only [v]
    infer_instance
  -- the unit on `X' ∖ f⁻¹ Z` is of étale origin, hence so is its extension by zero
  have hMo : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
      ((finiteCoefficientDerivedEquivalence _ T).functor.obj
        (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
          (overRestrict X' (I.comap f.left).support.compl).left) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj T) _))))) :=
    (isEtaleOrigin_of_isConstructible T (boundedConstructible_tensorUnit _ _)).plusEtaleOrigin
  have hjMo := ObjectProperty.prop_of_iso _
    ((finiteCoefficientDerivedOpenImmersionLowerShriekIso T j').app _)
    (plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek j' hMo)
  obtain ⟨e⟩ := nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso T f.left
    (overRestrictι X I.support.compl).left j' v hsq (centreι X I).left
    (isCompl_range_overRestrictι_centreι I).symm _ hjMo
  have hunit := isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism
    (Profinite.continuousMapRingObj T) v
  -- `Rv_* T̲ ≅ Rv_* Lv^* T̲ ≅ T̲`
  let e' : R((v)_*⟦Profinite.continuousMapRingObj T⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
    (R((v)_*⟦Profinite.continuousMapRingObj T⟧)).mapIso
      (leftDerivedUpperStarUnitIso _ v).symm ≪≫
      (asIso ((derivedUpperStarLowerStarAdjunction _ v).unit.app (𝟙_ _))).symm
  refine (nearbyCyclesVanishNear X I k' _ ζ).prop_of_iso
    (e ≪≫ (D(((overRestrictι X I.support.compl).left)_!open⟦
      Profinite.continuousMapRingObj T⟧)).mapIso e') ?_
  exact nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite T f I k' ζ _ hjMo h

end AlgebraicGeometry.ProEtale.CondensedRing
