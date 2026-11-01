/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperIntegralRationalScalarComparison
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat

/-! # Scalar endpoints for the constant projective-line calculation

Source: current blueprint, det-prop-scalar-six-direct-image.proof.md, localization
and filtered finite-subextension paragraphs; thm-amb-p1-decomposition.proof.md.
(blueprint: lem-pur-condensed-p1-scalar-endpoints)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxSize 4096

private theorem endpoint_from_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (F : A ⥤ C) (G : B ⥤ D) (α : L ⋙ G ≅ F ⋙ L')
    (β : R ⋙ F ⟶ G ⋙ R')
    (hb : β = mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.inv))
    (U : A) (V : C) (K : B) (K' : D)
    (c : L.obj U ≅ K) (d : L'.obj V ≅ K') (u : F.obj U ≅ V)
    [IsIso (β.app K)] :
    ∃ e : F.obj (R.obj K) ≅ R'.obj K',
      F.map (adj.unit.app U ≫ R.map c.hom) ≫ e.hom =
        u.hom ≫ adj'.unit.app V ≫ R'.map d.hom := by
  let v : G.obj K ≅ K' :=
    G.mapIso c.symm ≪≫ α.app U ≪≫ L'.mapIso u ≪≫ d
  refine ⟨asIso (β.app K) ≪≫ R'.mapIso v, ?_⟩
  have hunit := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.inv) U
  rw [← hb] at hunit
  change F.map (adj.unit.app U) ≫ β.app (L.obj U) =
    adj'.unit.app (F.obj U) ≫ R'.map (α.inv.app U) at hunit
  change F.map (adj.unit.app U ≫ R.map c.hom) ≫
    β.app K ≫ R'.map v.hom = _
  rw [F.map_comp, Category.assoc, ← Functor.comp_map R F,
    β.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Category.assoc, hunit]
  have hv : α.inv.app U ≫ G.map c.hom ≫ v.hom = L'.map u.hom ≫ d.hom := by
    dsimp only [v, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
    rw [← G.map_comp_assoc, c.hom_inv_id, G.map_id, Category.id_comp]
    simp only [Iso.inv_hom_id_app_assoc]
  simp only [Category.assoc]
  rw [← R'.map_comp, ← R'.map_comp, hv, R'.map_comp]
  exact (adj'.unit.naturality_assoc u.hom (R'.map d.hom)).symm

section PointwiseComposition
variable {A B C : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [MonObj B] [MonObj C]
  [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  (a : A ⟶ B) [IsMonHom a] (b : B ⟶ C) [IsMonHom b]

private theorem derived_push_comp_pointwise_isIso
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (a ≫ b) Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj A X)))
    (ha : IsIso ((derivedPushHom a f).app J))
    (hb : IsIso ((derivedPushHom b f).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj J))) :
    IsIso ((derivedPushHom (a ≫ b) f).app J) := by
  let : ∀ Z : Scheme.{u}, IsCommMonObj (condensedRingObj A Z) := fun Z ↦ inferInstance
  let : ∀ Z : Scheme.{u}, IsCommMonObj (condensedRingObj B Z) := fun Z ↦ inferInstance
  let : ∀ Z : Scheme.{u}, IsCommMonObj (condensedRingObj C Z) := fun Z ↦ inferInstance
  let : MonoidalCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X)) :=
    inferInstance
  let : MonoidalCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y)) :=
    inferInstance
  let : MonoidalCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) :=
    inferInstance
  let : MonoidalCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj B Y)) :=
    inferInstance
  let rx := exact_comp _ _ _ (restriction_comp a b X)
  let ry := exact_comp _ _ _ (restriction_comp a b Y)
  have hc := square_horizontal (lowerStar C f) (lowerStar B f) (lowerStar A f)
    (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap (a ≫ b) X))
    (Mod.comap (coefficientMap b Y)) (Mod.comap (coefficientMap a Y))
    (Mod.comap (coefficientMap (a ≫ b) Y))
    (comapLowerStarIso b f) (comapLowerStarIso a f)
    (comapLowerStarIso (a ≫ b) f) (restriction_comp a b X) (restriction_comp a b Y)
    (coefficient_square_comp a b f)
  have : IsIso ((Adjunction.pushHomOfComapIso
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
      (derivedComapLowerStarIso a f)).app J) := by
    simpa only [derivedPushHom] using ha
  have : IsIso ((Adjunction.pushHomOfComapIso
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b Y))
      (derivedComapLowerStarIso b f)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj J)) := by
    simpa only [derivedPushHom] using hb
  simpa only [derivedPushHom] using push_pasting_isIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (a ≫ b) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (a ≫ b) Y))
    (derivedComapLowerStarIso a f) (derivedComapLowerStarIso b f)
    (derivedComapLowerStarIso (a ≫ b) f) rx ry (by
      simpa only [derivedComapLowerStarIso, derived_square, rx, ry] using hc) J
end PointwiseComposition

private def scalar_unit_iso
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ := by
  let E := Mod.extendScalars (coefficientMap a X)
  letI : E.Monoidal := Mod.extendScalarsMonoidal (coefficientMap a X)
  letI : E.leftDerivedFunctor.Monoidal := E.leftDerivedFunctorMonoidal
  exact (Functor.Monoidal.εIso E.leftDerivedFunctor).symm

private theorem scalar_unit_isGE
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u}) :
    ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj (𝟙_ _)).IsGE 0 := by
  have : (𝟙_ (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj B X)))).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso (DerivedCategory.singleFunctorObjUnitIso _) 0
  exact DerivedCategory.TStructure.t.isGE_of_iso (scalar_unit_iso a X).symm 0

private theorem coefficient_factor (ℓ : ℕ) [Fact ℓ.Prime] :
    (DiagonalCoefficients.integralMap.{u} ℓ (DiagonalCoefficients.bottomField ℓ) ≫
      padicIntegersRingObjToContinuousMapRingObj ℓ (DiagonalCoefficients.bottomField ℓ)) ≫
      Profinite.padicSubfieldRingObjToPadicAlgCl ℓ (DiagonalCoefficients.bottomField ℓ) =
        Profinite.padicIntRingObjToPadicAlgCl ℓ := by
  ext T f
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rfl

private theorem coefficient_flat_of_eq
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    (a b : A ⟶ B) [IsMonHom a] [IsMonHom b] (h : a = b) (X : Scheme.{u})
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X)) := by
  subst b
  infer_instance

private theorem derived_push_isIso_of_eq
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
    (a b : A ⟶ B) [IsMonHom a] [IsMonHom b] (h : a = b)
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj A X)))
    (ha : IsIso ((derivedPushHom a f).app J)) :
    IsIso ((derivedPushHom b f).app J) := by
  subst b
  exact ha

attribute [local irreducible] Mod.extendScalars Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory

set_option maxHeartbeats 2000000 in
-- Rewriting and comparing the three actual coefficient extensions uses large derived types.
/-- Scalar extension of the direct-image endpoint, including the unit square for
a chosen scalar-unit endpoint.
This asserts no projective-line splitting.

Source: steps 5--9 of lem-pur-condensed-p1-constant-decomposition; current blueprint,
det-prop-scalar-six-direct-image.proof.md, localization and finite-field colimits.
(blueprint: lem-pur-condensed-p1-scalar-endpoints).

Proof: factor the actual integral inclusion through the bottom integral coefficient,
its fraction field, and the algebraic closure. The first coefficient map is the
normalized base-coefficient isomorphism. The coefficient unit is bounded below.
Apply localizedDirectImageComparison_isIso to localization and
isIso_derivedPushHom_padicAlgCl_of_boundedBelow to algebraic-closure extension.
These are the actual scalar mates; they already implement bounded continuity for
the two coefficient colimits. All coefficient extensions are exact. Their derived
composition is therefore extension along the actual integral-to-closure map.
Compose the invertible comparisons and the coefficient-unit identifications.
Choose normalized coefficient-unit endpoints using the flat-source endpoint theorem.
The scalar_unit_push identity transports the ordinary coefficient-unit arrow.
The canonical single-complex/adjunction comparison identifies that arrow with the
actual total-derived unit followed by leftDerivedUpperStarUnitIso. Thus the
composite comparison has the required square for the normalized unit endpoint u0.
For a given u, let w be u0.inv followed by u.hom. Conjugate its geometric pullback by
the new pullback-unit isomorphism and postcompose the direct-image endpoint with
the direct image of that automorphism. Naturality of the geometric adjunction unit
gives the square with u. Every correction is invertible. This works for every S,
including an empty scheme, without invertibility of ell on S or a finite
cohomological-dimension hypothesis. -/
theorem condensed_projectiveLine_scalar_endpoints
    (ℓ : ℕ) [Fact ℓ.Prime] (S : Scheme.{u}) :
    let C := Profinite.continuousMapRingObj.{u} ℤ_[ℓ]
    let R := Profinite.padicAlgClRingObj.{u} ℓ
    let M := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj C S)
    let F := (Mod.extendScalars
      (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) S)).leftDerivedFunctor
    ∀ u : F.obj (𝟙_ (DerivedCategory M)) ≅ 𝟙_ _,
    ∃ e : F.obj ((moduleObjectDerivedPushforward C (ProjectiveLine S ↘ S)).obj
        (𝟙_ _)) ≅ (moduleObjectDerivedPushforward R (ProjectiveLine S ↘ S)).obj (𝟙_ _),
      F.map ((derivedUpperStarLowerStarAdjunction C
          (ProjectiveLine S ↘ S)).unit.app (𝟙_ _) ≫
        (moduleObjectDerivedPushforward C (ProjectiveLine S ↘ S)).map
          (leftDerivedUpperStarUnitIso C (ProjectiveLine S ↘ S)).hom) ≫ e.hom =
      u.hom ≫ (derivedUpperStarLowerStarAdjunction R
          (ProjectiveLine S ↘ S)).unit.app (𝟙_ _) ≫
        (moduleObjectDerivedPushforward R (ProjectiveLine S ↘ S)).map
          (leftDerivedUpperStarUnitIso R (ProjectiveLine S ↘ S)).hom := by
  dsimp only
  intro u
  let q := ProjectiveLine S ↘ S
  let E := DiagonalCoefficients.bottomField ℓ
  let a := DiagonalCoefficients.integralMap.{u} ℓ E
  let b := padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E
  let c := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E
  let K := 𝟙_ (DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology (ProjectiveLine S)) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) (ProjectiveLine S))))
  obtain ⟨hf, hi⟩ := DiagonalCoefficients.integralScalarComparison_isIso ℓ E q
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap a T)) := hf
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap b T)) :=
    fun T ↦ preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield ℓ E T
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap c T)) :=
    fun T ↦ preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ T E
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (a ≫ b) T)) :=
    fun T ↦ coefficient_comp_flat a b T
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap ((a ≫ b) ≫ c) T)) :=
    fun T ↦ coefficient_comp_flat (a ≫ b) c T
  let : ∀ T : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) T)) :=
    fun T ↦ coefficient_flat_of_eq ((a ≫ b) ≫ c)
      (Profinite.padicIntRingObjToPadicAlgCl ℓ) (coefficient_factor ℓ) T
  have h0 : IsIso (derivedPushHom a q) := hi
  have : ((Mod.extendScalars (coefficientMap a (ProjectiveLine S))).leftDerivedFunctor.obj
      K).IsGE 0 := scalar_unit_isGE a (ProjectiveLine S)
  have h1 : IsIso ((derivedPushHom b q).app
      ((Mod.extendScalars (coefficientMap a (ProjectiveLine S))).leftDerivedFunctor.obj K)) :=
    isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E q _ 0
  have h2 : IsIso ((derivedPushHom (a ≫ b) q).app K) :=
    derived_push_comp_pointwise_isIso a b q K
      (NatIso.isIso_app_of_isIso (derivedPushHom a q) K) h1
  have : ((Mod.extendScalars (coefficientMap (a ≫ b)
      (ProjectiveLine S))).leftDerivedFunctor.obj K).IsGE 0 :=
    scalar_unit_isGE (a ≫ b) (ProjectiveLine S)
  have h3 : IsIso ((derivedPushHom c q).app
      ((Mod.extendScalars (coefficientMap (a ≫ b)
        (ProjectiveLine S))).leftDerivedFunctor.obj K)) :=
    isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E q ⟨_, 0, inferInstance⟩
  have h4 : IsIso ((derivedPushHom ((a ≫ b) ≫ c) q).app K) :=
    derived_push_comp_pointwise_isIso (a ≫ b) c q K h2 h3
  have : IsIso ((derivedPushHom (Profinite.padicIntRingObjToPadicAlgCl ℓ) q).app K) :=
    derived_push_isIso_of_eq ((a ≫ b) ≫ c) (Profinite.padicIntRingObjToPadicAlgCl ℓ)
      (coefficient_factor ℓ) q K h4
  exact endpoint_from_mate
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj ℤ_[ℓ]) q)
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) q)
    _ _ (derivedPullIso (Profinite.padicIntRingObjToPadicAlgCl ℓ) q)
    (derivedPushHom (Profinite.padicIntRingObjToPadicAlgCl ℓ) q)
    (derivedPushHom_eq_mateEquiv (Profinite.padicIntRingObjToPadicAlgCl ℓ) q)
    (𝟙_ _) (𝟙_ _) K (𝟙_ _)
    (leftDerivedUpperStarUnitIso (Profinite.continuousMapRingObj ℤ_[ℓ]) q)
    (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) q) u

end AlgebraicGeometry.ProEtale.CondensedRing
