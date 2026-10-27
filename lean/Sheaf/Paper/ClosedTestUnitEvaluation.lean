/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit
import all Sheaf.AlgebraicGeometry.ProEtaleSpecializationAffineCoordinates
import Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import all Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison

/-!
# Internal normalization and actual closed-test units

Source: Stacks Project, proetale.tex, Tags 09BK and 09BL (1)--(2);
sites-modules.tex, Tags 03D2, 03D3, 03D6, 03D7; derived.tex, Tag 08BJ.
(blueprint: lem-sfb-closed-test-unit-evaluation).

The closed-evaluation comparison below is normalized on the actual adjunction unit.
Its inverse on a contractible test is therefore the closed-evaluation identification,
with both the coefficient action and restriction maps retained.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.AffineProEt
open AlgebraicGeometry.ProEtale.InternalModuleOperations

namespace AlgebraicGeometry.ProEtale.ClosedTest

/-- The quotient closed immersion used by the closed-site lift.
Source: Stacks 09BK (blueprint: lem-sfb-closed-test-unit-evaluation). -/
abbrev immersion (A : Type u) [CommRing A] (I : Ideal A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The canonical identification V = v(V) times_U Z, using the recorded pullback square.
Source: Stacks 09BK (blueprint: lem-sfb-closed-test-unit-evaluation). -/
def fiberIso (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).obj V ≅
      (siteMap (immersion A I)).obj
        ((AffineProEt.toProEt (Spec (.of A))).obj ((closedSiteLift A I).obj V)) :=
  MorphismProperty.Over.isoMk
    (((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.1.isoPullback)
    (((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.1.isoPullback_hom_snd)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Sections on the lifted affine tests, before sheafification.
Source: Stacks 09BL (1) (blueprint: lem-sfb-closed-test-unit-evaluation). -/
abbrev liftSections (A : Type u) [CommRing A] (I : Ideal A) :=
  Mod.forget (condensedRingObj Λ (Spec (.of A))) ⋙
    sheafToPresheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
        (closedSiteLift A I ⋙ AffineProEt.toProEt (Spec (.of A))).op

/-- The actual internal inverse image, restricted to the affine basis.
Source: Stacks 09BL (1) (blueprint: lem-sfb-closed-test-unit-evaluation). -/
abbrev inverseBasis (A : Type u) [CommRing A] (I : Ideal A) :=
  CondensedRing.upperStar Λ (immersion A I) ⋙
    Mod.forget (condensedRingObj Λ (Spec (.of (A ⧸ I)))) ⋙
      (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous Ab.{u + 1}
        (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I))))

/-- The actual internal adjunction-unit section, transported from u(v(V)) to V.
Source: Stacks 03D3 and 09BL (2)
(blueprint: lem-sfb-closed-test-unit-evaluation). -/
def unitSection (A : Type u) [CommRing A] (I : Ideal A)
    (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A))))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    F.X.obj.obj (op ((AffineProEt.toProEt (Spec (.of A))).obj ((closedSiteLift A I).obj V))) →+
      ((inverseBasis Λ A I).obj F).obj.obj (op V) :=
  (((CondensedRing.upperStar Λ (immersion A I)).obj F).X.obj.map
    (fiberIso A I V).hom.op).hom.comp
      (((CondensedRing.upperStarLowerStarAdjunction Λ (immersion A I)).unit.app F).hom.hom.app
        (op ((AffineProEt.toProEt (Spec (.of A))).obj ((closedSiteLift A I).obj V)))).hom

/-- The scalar map Lambda_U(v(V)) to Lambda_Z(V), with the same fibre identification.
Source: Stacks 03D3 and 09BK
(blueprint: lem-sfb-closed-test-unit-evaluation). -/
def scalarSection (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  ((ring Λ (Spec (.of (A ⧸ I)))).obj.map (fiberIso A I V).hom.op).hom.comp
    (((coefficientMap Λ (immersion A I)).hom.app
      (op ((AffineProEt.toProEt (Spec (.of A))).obj ((closedSiteLift A I).obj V)))).hom)

attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction

private instance basis_continuous (T : Scheme.{u}) :
    (AffineProEt.toProEt T).IsContinuous (topology T) (ProEt.topology T) := inferInstance

private instance basis_equivalence (T : Scheme.{u}) :
    ((AffineProEt.toProEt T).sheafPushforwardContinuous Ab.{u + 1}
      (topology T) (ProEt.topology T)).IsEquivalence := inferInstance

private def underlyingPullbackIso {X Y : Scheme.{u}} (b : X ⟶ Y) :
    CondensedRing.upperStar Λ b ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ ProEtale.upperStar Ab.{u + 1} b :=
  Functor.isoWhiskerLeft
    ((ProEtale.upperStar Ab.{u + 1} b).mapMod (condensedRingObj Λ Y))
    (Functor.isoWhiskerRight (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ b))
      (Mod.forget (condensedRingObj Λ X)))

private theorem underlyingPullbackIso_unit {X Y : Scheme.{u}} (b : X ⟶ Y)
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} b).map ((underlyingPullbackIso Λ b).hom.app F) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} b).unit.app F.X := by
  have h := CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom Λ b F
    ((CondensedRing.upperStar Λ b).obj F) (𝟙 _)
  rw [Adjunction.homEquiv_id] at h
  change ((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom =
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} b).unit.app F.X ≫
      (ProEtale.lowerStar Ab.{u + 1} b).map
        (Mod.extendUnitHom (condensedPullbackHom Λ b)
          (((ProEtale.upperStar Ab.{u + 1} b).mapMod (condensedRingObj Λ Y)).obj F) ≫ 𝟙 _) at h
  rw [Category.comp_id] at h
  calc
    _ = ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} b).unit.app F.X ≫
        (ProEtale.lowerStar Ab.{u + 1} b).map
          (Mod.extendUnitHom (condensedPullbackHom Λ b)
            (((ProEtale.upperStar Ab.{u + 1} b).mapMod (condensedRingObj Λ Y)).obj F))) ≫
        (ProEtale.lowerStar Ab.{u + 1} b).map
          ((underlyingPullbackIso Λ b).hom.app F) := congrArg (fun z ↦ z ≫ _) h
    _ = _ := by
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
      change _ ≫ (ProEtale.lowerStar Ab.{u + 1} b).map
        (Mod.extendUnitHom (condensedPullbackHom Λ b) _ ≫
          ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ b)).hom.app _).hom) = _
      rw [CondensedRing.extendUnitHom_extendScalarsIsoComapInv_hom_app]
      change _ ≫ (ProEtale.lowerStar Ab.{u + 1} b).map (𝟙 _) = _
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      rfl

private theorem underlyingPullbackIso_inv_unit {X Y : Scheme.{u}} (b : X ⟶ Y)
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} b).unit.app F.X ≫
      (ProEtale.lowerStar Ab.{u + 1} b).map ((underlyingPullbackIso Λ b).inv.app F) =
      ((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom := by
  rw [← underlyingPullbackIso_unit Λ b F, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  change ((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom ≫
    (ProEtale.lowerStar Ab.{u + 1} b).map
      (𝟙 ((CondensedRing.upperStar Λ b).obj F).X) = _
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

attribute [local irreducible] proEtaleModuleInverseImage

private theorem canonicalUnit_inverseSection {X Y : Scheme.{u}} (b : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (W : Y.ProEt) (x : M.val.obj (op W)) :
    ((canonicalAdjunction b R).unit.app M).val.app (op W) x =
      ProEtaleTensorComparison.inverseSection b M W x :=
  canonicalUnit_sections b R M (op W) x

attribute [local irreducible] ProEtaleTensorComparison.inverseSection

@[irreducible] private def ordinaryUnderlyingComparison {X Y : Scheme.{u}} (b : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.toSheaf.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
        proEtaleSheafInverseImage b Ab.{u + 1} ⟶
      ProEtaleTensorComparison.inverse b R ⋙
        SheafOfModules.toSheaf.{u + 1} ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ProEtaleTensorComparison.inverseRing b R)) :=
  by
  let P := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ProEtaleTensorComparison.inverseRing b R))
  let L := ProEtaleTensorComparison.inverse b R
  let a := proEtaleSheafAdjunction b Ab.{u + 1}
  let eta : P ⟶ L ⋙ Q ⋙ proEtaleSheafDirectImage b Ab.{u + 1} :=
    { app := fun M ↦ P.map ((canonicalAdjunction b R).unit.app M)
      naturality := by
        intro M N f
        ext W m
        exact congrArg (fun g ↦ g.val.app W m)
          ((canonicalAdjunction b R).unit.naturality f) }
  exact ((a.whiskerRight _).homEquiv P (L ⋙ Q)).symm eta

private theorem ordinaryUnderlyingComparison_app {X Y : Scheme.{u}} (b : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (ordinaryUnderlyingComparison b R).app M =
      ((proEtaleSheafAdjunction b Ab.{u + 1}).homEquiv
        ((SheafOfModules.toSheaf _).obj M)
        ((SheafOfModules.toSheaf _).obj
          ((ProEtaleTensorComparison.inverse b R).obj M))).symm
            ((SheafOfModules.toSheaf _).map ((canonicalAdjunction b R).unit.app M)) := by
  rw [ordinaryUnderlyingComparison]
  rfl

private theorem ordinaryUnderlyingComparison_isIso {X Y : Scheme.{u}} (b : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    IsIso (ordinaryUnderlyingComparison b R) := by
  have : ∀ M, IsIso ((ordinaryUnderlyingComparison b R).app M) := by
    intro M
    rw [ordinaryUnderlyingComparison_app]
    exact proEtaleModuleInverseImage_unitComparison_isIso b R (canonicalAdjunction b R) M
  exact NatIso.isIso_of_isIso_app _

private theorem ordinaryUnderlyingComparison_unit {X Y : Scheme.{u}} (b : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (W : Y.ProEt) (x : M.val.obj (op W)) :
    ((ordinaryUnderlyingComparison b R).app M).hom.app (op ((siteMap b).obj W))
      (((proEtaleSheafAdjunction b Ab.{u + 1}).unit.app
        ((SheafOfModules.toSheaf _).obj M)).hom.app (op W) x) =
      ProEtaleTensorComparison.inverseSection b M W x := by
  let P := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ProEtaleTensorComparison.inverseRing b R))
  have h := ((proEtaleSheafAdjunction b Ab.{u + 1}).homEquiv
    (P.obj M) (Q.obj ((ProEtaleTensorComparison.inverse b R).obj M))).apply_symm_apply
      (P.map ((canonicalAdjunction b R).unit.app M))
  rw [← ordinaryUnderlyingComparison_app b R M, Adjunction.homEquiv_unit] at h
  have hx := congrArg (fun g ↦ g.hom.app (op W) x) h
  change _ = ((canonicalAdjunction b R).unit.app M).val.app (op W) x at hx
  rw [canonicalUnit_inverseSection] at hx
  exact hx

attribute [local irreducible] CondensedRing.upperStar

private theorem full_test_surjective (T : Scheme.{u}) (V : T.AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    (P Q : Sheaf (ProEt.topology T) (Type (u + 1))) (f : P ⟶ Q) (hf : Epi f) :
    Function.Surjective (f.hom.app (op ((AffineProEt.toProEt T).obj V))) := by
  exact ProEt.isWeaklyContractible_of_iso V.left.isoSpec f
    ((Sheaf.isLocallySurjective_iff_epi f).mpr hf)

private theorem basis_test_surjective_of_full (T : Scheme.{u}) (V : T.AffineProEt)
    (hV : ∀ (P Q : Sheaf (ProEt.topology T) (Type (u + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op ((AffineProEt.toProEt T).obj V))))
    (P Q : Sheaf (topology T) (Type (u + 1))) (f : P ⟶ Q) (hf : Epi f) :
    Function.Surjective (f.hom.app (op V)) := by
  let R := (AffineProEt.toProEt T).sheafPushforwardContinuous (Type (u + 1))
    (topology T) (ProEt.topology T)
  let E := R.asEquivalence
  have := hf
  intro x
  obtain ⟨y, hy⟩ := hV _ _ (E.inverse.map f) inferInstance
    ((E.counitIso.inv.app Q).hom.app (op V) x)
  refine ⟨(E.counitIso.hom.app P).hom.app (op V) y, ?_⟩
  have h := congrArg (fun g ↦ g.hom.app (op V) y) (E.counitIso.hom.naturality f)
  change (E.counitIso.hom.app Q).hom.app (op V)
      (((E.inverse.map f).hom.app (op ((AffineProEt.toProEt T).obj V))) y) =
    f.hom.app (op V) ((E.counitIso.hom.app P).hom.app (op V) y) at h
  rw [← h, hy]
  exact congrArg (fun g ↦ g.hom.app (op V) x) (E.counitIso.inv_hom_id_app Q)

private theorem basis_test_surjective (T : Scheme.{u}) (V : T.AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    (P Q : Sheaf (topology T) (Type (u + 1))) (f : P ⟶ Q) (hf : Epi f) :
    Function.Surjective (f.hom.app (op V)) :=
  basis_test_surjective_of_full T V (full_test_surjective T V) P Q f hf

private theorem internal_test_preservesHomology (T : Scheme.{u}) (V : T.AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)] :
    (Mod.forget (condensedRingObj Λ T) ⋙
      sheafToPresheaf (ProEt.topology T) Ab.{u + 1} ⋙
      (CategoryTheory.evaluation _ _).obj
        (op ((AffineProEt.toProEt T).obj V))).PreservesHomology := by
  have := (internal_module_operations_transport Λ).1 T |>.1
  have := ProEt.weaklyContractible_evaluation_preservesHomology T
    (sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T) (condensedRingObj Λ T))
    ((AffineProEt.toProEt T).obj V) (full_test_surjective T V)
  have : (equivalence Λ T).functor.PreservesHomology := inferInstance
  have : (SheafOfModules.evaluation (ring Λ T)
      (op ((AffineProEt.toProEt T).obj V))).PreservesHomology := by assumption
  have : (SheafOfModules.evaluation (ring Λ T)
      (op ((AffineProEt.toProEt T).obj V))).Additive := by
    constructor
    intro M N f g
    rfl
  have := CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology
    (SheafOfModules.evaluation (ring Λ T) (op ((AffineProEt.toProEt T).obj V)))
  have := CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology
    (SheafOfModules.evaluation (ring Λ T) (op ((AffineProEt.toProEt T).obj V)))
  let D := forget₂ (ModuleCat.{u + 1}
    ((ring Λ T).obj.obj (op ((AffineProEt.toProEt T).obj V)))) Ab.{u + 1}
  have : PreservesFiniteLimits D := inferInstance
  have : PreservesColimitsOfSize.{0, 0} D :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} _
  have : PreservesFiniteColimits D := PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} D
  have h : ((equivalence Λ T).functor ⋙
      SheafOfModules.evaluation.{u + 1} (ring Λ T)
        (op ((AffineProEt.toProEt T).obj V)) ⋙ D).PreservesHomology := inferInstance
  exact h

private theorem local_test_counit (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(((closedSiteLift A I).obj V).left, ⊤)]
    (adj : closedSiteLift (Γ(((closedSiteLift A I).obj V).left, ⊤))
        (RingHom.ker (closedSiteLiftInclusion A I V).appTop.hom) ⊣
      closedSiteBaseChange (Γ(((closedSiteLift A I).obj V).left, ⊤))
        (RingHom.ker (closedSiteLiftInclusion A I V).appTop.hom)) :
    IsIso (adj.counit.app (AffineProEt.mk (𝟙 _) (proAffineEtale.of_isAffine _))) := by
  let B := ((closedSiteLift A I).obj V).left
  let U := AffineProEt.mk (𝟙 (Spec Γ(B, ⊤))) (proAffineEtale.of_isAffine _)
  have hclosed := (affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V |>.1
  have hspec := (affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V |>.2.2
  have : IsClosedImmersion (closedSiteLiftInclusion A I V) := hclosed
  apply isIso_closedSiteCounit_of_specialization _ _ adj U
  · apply basis_test_surjective_of_full
    intro P Q f hf
    exact ProEt.isWeaklyContractible_of_iso (R := Γ(B, ⊤)) (Iso.refl _) f
      ((Sheaf.isLocallySurjective_iff_epi f).mpr hf)
  · exact quotient_specialization (closedSiteLiftInclusion A I V) hspec

private def liftAdjunction (A : Type u) [CommRing A] (I : Ideal A) :
    closedSiteLift A I ⊣ closedSiteBaseChange A I := by
  let e V U := Equiv.ofBijective (siteHomMap A I V U) (siteHomMap_bijective A I V U)
  exact Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro V W U f g
        apply (e V U).injective
        change siteHomMap A I V U _ = siteHomMap A I V U _
        rw [siteHomMap_naturality_left]
        exact (e V U).apply_symm_apply (f ≫ g) |>.trans
          (congrArg (fun k ↦ f ≫ k) ((e W U).apply_symm_apply g)).symm
      homEquiv_naturality_right := siteHomMap_naturality_right A I }

private theorem liftAdjunction_unit (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    (AffineProEt.toProEt _).map ((liftAdjunction A I).unit.app V) =
      (fiberIso A I V).hom := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (closedSiteLiftInclusion A I V ≫ 𝟙 _) V.hom _ =
    (inclusion_pullback A I V).isoPullback.hom
  apply pullback.hom_ext
  · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst, Category.comp_id]
  · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]

private theorem closedBaseChange_continuous (A : Type u) [CommRing A] (I : Ideal A) :
    (closedSiteBaseChange A I).IsContinuous
      (topology (Spec (.of A))) (topology (Spec (.of (A ⧸ I)))) := by
  have : (closedSiteLift A I).IsCocontinuous
      (topology (Spec (.of (A ⧸ I)))) (topology (Spec (.of A))) :=
    (affine_closed_site_functor_properties A I).2.2.2.2.1
  exact (liftAdjunction A I).isContinuous_of_isCocontinuous _ _

private def sheafPrecompositionAdjunction
    {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [R.IsContinuous K J] [HasSheafify J Ab.{u + 1}] :
    (sheafToPresheaf K Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj L.op ⋙
      presheafToSheaf J Ab.{u + 1}) ⊣ R.sheafPushforwardContinuous Ab.{u + 1} K J :=
  ((adj.op.whiskerLeft Ab.{u + 1}).comp
    (sheafificationAdjunction J Ab.{u + 1})).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf K _))
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

private theorem sheafPrecompositionAdjunction_transpose
    {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [R.IsContinuous K J] [HasSheafify J Ab.{u + 1}]
    (F : Sheaf K Ab.{u + 1}) (G : Sheaf J Ab.{u + 1})
    (f : (presheafToSheaf J Ab.{u + 1}).obj (L.op ⋙ F.obj) ⟶ G) :
    (((sheafPrecompositionAdjunction J K L R adj).homEquiv F G) f).hom =
      ((adj.op.whiskerLeft Ab.{u + 1}).homEquiv F.obj G.obj)
        (((sheafificationAdjunction J Ab.{u + 1}).homEquiv (L.op ⋙ F.obj) G) f) := by
  simp only [sheafPrecompositionAdjunction, Adjunction.restrictFullyFaithful,
    Adjunction.mkOfHomEquiv_homEquiv, Adjunction.comp_homEquiv, Functor.FullyFaithful.id]
  exact (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf K Ab.{u + 1})).map_preimage _

private def basisLiftAdjunction (A : Type u) [CommRing A] (I : Ideal A) :
    letI := closedBaseChange_continuous A I
    (sheafToPresheaf (topology (Spec (.of A))) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj (closedSiteLift A I).op ⋙
      presheafToSheaf (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}) ⊣
    (closedSiteBaseChange A I).sheafPushforwardContinuous Ab.{u + 1}
      (topology (Spec (.of A))) (topology (Spec (.of (A ⧸ I)))) :=
  by
  let := closedBaseChange_continuous A I
  exact sheafPrecompositionAdjunction _ _ _ _ (liftAdjunction A I)

private theorem basisLiftAdjunction_transpose (A : Type u) [CommRing A] (I : Ideal A)
    (F : Sheaf (topology (Spec (.of A))) Ab.{u + 1})
    (G : Sheaf (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1})
    (f : (presheafToSheaf (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}).obj
      ((closedSiteLift A I).op ⋙ F.obj) ⟶ G) :
    (((basisLiftAdjunction A I).homEquiv F G) f).hom =
      (((liftAdjunction A I).op.whiskerLeft Ab.{u + 1}).homEquiv F.obj G.obj)
        (((sheafificationAdjunction (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}).homEquiv
          ((closedSiteLift A I).op ⋙ F.obj) G) f) :=
  by
  let := closedBaseChange_continuous A I
  exact sheafPrecompositionAdjunction_transpose _ _ _ _ (liftAdjunction A I) F G f

private def abelianBasisComparison (A : Type u) [CommRing A] (I : Ideal A) :
    sheafToPresheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
        (closedSiteLift A I ⋙ AffineProEt.toProEt (Spec (.of A))).op ⋙
      presheafToSheaf (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1} ≅
    ProEtale.upperStar Ab.{u + 1} (immersion A I) ⋙
      (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous Ab.{u + 1}
        (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I)))) := by
  let RX := (AffineProEt.toProEt (Spec (.of A))).sheafPushforwardContinuous Ab.{u + 1}
    (topology (Spec (.of A))) (ProEt.topology (Spec (.of A)))
  let RZ := (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous Ab.{u + 1}
    (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I))))
  let := closedBaseChange_continuous A I
  let R := (closedSiteBaseChange A I).sheafPushforwardContinuous Ab.{u + 1}
    (topology (Spec (.of A))) (topology (Spec (.of (A ⧸ I))))
  let beta : ProEtale.lowerStar Ab.{u + 1} (immersion A I) ⋙ RX ≅ RZ ⋙ R := Iso.refl _
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (immersion A I)
  let b := basisLiftAdjunction A I
  let alpha := ((mateEquiv a b).symm beta.hom).natTrans
  have : IsIso alpha := isIso_inverseMate_of_equivalences a b beta
  exact asIso alpha

private theorem abelianBasisComparison_unit (A : Type u) [CommRing A] (I : Ideal A)
    (F : Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (x : F.obj.obj (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)))) :
    ((abelianBasisComparison A I).hom.app F).hom.app (op V)
        (((toSheafify (topology (Spec (.of (A ⧸ I))))
          ((closedSiteLift A I ⋙ AffineProEt.toProEt (Spec (.of A))).op ⋙ F.obj)).app
            (op V)) x) =
      (((ProEtale.upperStar Ab.{u + 1} (immersion A I)).obj F).obj.map
        (fiberIso A I V).hom.op)
        (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (immersion A I)).unit.app F).hom.app
          (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))) x) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let RX := (AffineProEt.toProEt X).sheafPushforwardContinuous Ab.{u + 1}
    (topology X) (ProEt.topology X)
  let RZ := (AffineProEt.toProEt Z).sheafPushforwardContinuous Ab.{u + 1}
    (topology Z) (ProEt.topology Z)
  let := closedBaseChange_continuous A I
  let R := (closedSiteBaseChange A I).sheafPushforwardContinuous Ab.{u + 1}
    (topology X) (topology Z)
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (immersion A I)
  let b := basisLiftAdjunction A I
  let beta : ProEtale.lowerStar Ab.{u + 1} (immersion A I) ⋙ RX ≅ RZ ⋙ R := Iso.refl _
  let G := RZ.obj ((ProEtale.upperStar Ab.{u + 1} (immersion A I)).obj F)
  let f := (abelianBasisComparison A I).hom.app F
  have h := unit_mateEquiv_symm a b (.mk _ _ _ _ beta.hom) F
  change RX.map (a.unit.app F) ≫ 𝟙 _ = b.unit.app (RX.obj F) ≫ R.map f at h
  rw [Category.comp_id] at h
  have hhom : (b.homEquiv (RX.obj F) G f).hom = (RX.map (a.unit.app F)).hom := by
    rw [Adjunction.homEquiv_unit]
    exact congrArg (fun g : RX.obj F ⟶ R.obj G ↦ g.hom) h.symm
  rw [basisLiftAdjunction_transpose] at hhom
  have ht := congrArg
    (((liftAdjunction A I).op.whiskerLeft Ab.{u + 1}).homEquiv (RX.obj F).obj G.obj).symm hhom
  change (((liftAdjunction A I).op.whiskerLeft Ab.{u + 1}).homEquiv
    (RX.obj F).obj G.obj).symm
      ((((liftAdjunction A I).op.whiskerLeft Ab.{u + 1}).homEquiv
        (RX.obj F).obj G.obj) _) = _ at ht
  rw [Equiv.symm_apply_apply] at ht
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at ht
  have hx := congrArg (fun g ↦ g.app (op V) x) ht
  change _ = G.obj.map ((liftAdjunction A I).unit.app V).op
    (((a.unit.app F).hom.app (op ((AffineProEt.toProEt X).obj ((closedSiteLift A I).obj V)))) x)
    at hx
  change f.hom.app (op V)
    (((toSheafify (topology Z) ((closedSiteLift A I).op ⋙ (RX.obj F).obj)).app
      (op V)) x) =
      (((ProEtale.upperStar Ab.{u + 1} (immersion A I)).obj F).obj.map
        ((AffineProEt.toProEt Z).map ((liftAdjunction A I).unit.app V)).op)
        (((a.unit.app F).hom.app
          (op ((AffineProEt.toProEt X).obj ((closedSiteLift A I).obj V)))) x) at hx
  rw [liftAdjunction_unit] at hx
  exact hx

private def closedComparison (A : Type u) [CommRing A] (I : Ideal A) :
    liftSections Λ A I ⋙ presheafToSheaf (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1} ≅
      inverseBasis Λ A I :=
  Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ (Spec (.of A))))
      (abelianBasisComparison A I) ≪≫
    Functor.isoWhiskerRight (underlyingPullbackIso Λ (immersion A I)).symm
      ((AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous Ab.{u + 1}
        (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I)))))

attribute [local irreducible] fiberIso

private theorem closedComparison_unit (A : Type u) [CommRing A] (I : Ideal A)
    (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A))))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (x : ((liftSections Λ A I).obj F).obj (op V)) :
    ((closedComparison Λ A I).hom.app F).hom.app (op V)
        (((toSheafify (topology (Spec (.of (A ⧸ I))))
          ((liftSections Λ A I).obj F)).app (op V)) x) = unitSection Λ A I F V x := by
  change ((underlyingPullbackIso Λ (immersion A I)).inv.app F).hom.app
    (op ((AffineProEt.toProEt _).obj V))
      (((abelianBasisComparison A I).hom.app F.X).hom.app (op V)
        (((toSheafify (topology (Spec (.of (A ⧸ I))))
          ((closedSiteLift A I ⋙ AffineProEt.toProEt (Spec (.of A))).op ⋙ F.X.obj)).app
            (op V)) x)) = _
  rw [abelianBasisComparison_unit]
  erw [NatTrans.naturality_apply
    (((underlyingPullbackIso Λ (immersion A I)).inv.app F).hom)
    (fiberIso A I V).hom.op]
  have h := congrArg (fun g ↦ g.hom.app
    (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))) x)
      (underlyingPullbackIso_inv_unit Λ (immersion A I) F)
  exact congrArg
    (((CondensedRing.upperStar Λ (immersion A I)).obj F).X.obj.map
      (fiberIso A I V).hom.op) h

private theorem specializes_pullback {X Y T : Scheme.{u}} (b : X ⟶ Y)
    (W : Y.ProEt) (k : T ⟶ W.left) (p : T ⟶ X)
    (hp : IsPullback k p W.hom b)
    (hs : ∀ x : W.left, ∃ z : T, Specializes x (k z)) :
    ∀ x : W.left, ∃ z : ↥(pullback W.hom b),
      Specializes x ((pullback.fst W.hom b) z) := by
  intro x
  obtain ⟨z, hz⟩ := hs x
  refine ⟨hp.isoPullback.hom z, ?_⟩
  have h := congrArg (fun f : T ⟶ W.left ↦ f z) hp.isoPullback_hom_fst
  exact h ▸ hz

private theorem internalUnit_bijective {X Y : Scheme.{u}} (b : X ⟶ Y)
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (W : Y.ProEt)
    (hunit : Function.Bijective
      (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} b).unit.app F.X).hom.app
        (op W))) :
    Function.Bijective
      (((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom.hom.app
        (op W)) := by
  have hu := congrArg (fun f ↦ f.hom.app (op W))
    (underlyingPullbackIso_inv_unit Λ b F)
  change
    (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} b).unit.app F.X).hom.app
      (op W)) ≫ (((underlyingPullbackIso Λ b).inv.app F).hom.app
        (op ((siteMap b).obj W))) =
      (((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom.hom.app
        (op W)) at hu
  rw [← hu]
  exact (ConcreteCategory.bijective_of_isIso
    (((underlyingPullbackIso Λ b).inv.app F).hom.app
      (op ((siteMap b).obj W)))).comp hunit

attribute [local irreducible] closedSiteLift closedSiteBaseChange

private theorem internalSpecializationUnit_bijective {X Y : Scheme.{u}}
    (b : X ⟶ Y) [IsClosedImmersion b] (W : Y.ProEt) [IsAffine W.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology Y) (Type (u + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op W)))
    (hspec : ∀ x : W.left, ∃ z : ↥(pullback W.hom b),
      Specializes x ((pullback.fst W.hom b) z))
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Function.Bijective
      (((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom.hom.app
        (op W)) := by
  let tau := Functor.whiskerRight (proEtaleSheafAdjunction b Ab.{u + 1}).unit
    ((sheafSections (ProEt.topology Y) Ab.{u + 1}).obj (op W))
  let : IsIso tau := isIso_proEtaleUnit_sections_of_specialization b W hweak hspec
  have h := ConcreteCategory.bijective_of_isIso (tau.app F.X)
  exact internalUnit_bijective Λ b F W h

private theorem internalSpecializationRestriction_bijective {X Y T : Scheme.{u}}
    (b : X ⟶ Y) [IsClosedImmersion b] (W : Y.ProEt) [IsAffine W.left]
    (V : X.ProEt) (k : T ⟶ W.left) (p : T ⟶ X)
    (hp : IsPullback k p W.hom b)
    (hs : ∀ x : W.left, ∃ z : T, Specializes x (k z))
    (e : V ≅ (siteMap b).obj W)
    (hweak : ∀ (P Q : Sheaf (ProEt.topology Y) (Type (u + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op W)))
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Function.Bijective (fun x ↦
      ((CondensedRing.upperStar Λ b).obj F).X.obj.map e.hom.op
        (((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom.hom.app
          (op W) x)) := by
  exact (ConcreteCategory.bijective_of_isIso
    (((CondensedRing.upperStar Λ b).obj F).X.obj.map e.hom.op)).comp
      (internalSpecializationUnit_bijective Λ b W hweak
        (specializes_pullback b W k p hp hs) F)

private theorem unitSection_bijective (A : Type u) [CommRing A] (I : Ideal A)
    (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A))))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(((closedSiteLift A I).obj V).left, ⊤)] :
    Function.Bijective (unitSection Λ A I F V) := by
  have : IsClosedImmersion (immersion A I) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  have : IsAffine
      ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)).left :=
    inferInstanceAs (IsAffine ((closedSiteLift A I).obj V).left)
  exact internalSpecializationRestriction_bijective Λ (immersion A I)
    ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))
    ((AffineProEt.toProEt _).obj V) (closedSiteLiftInclusion A I V) V.hom
    ((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.1
    ((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.2
    (fiberIso A I V) (full_test_surjective _ ((closedSiteLift A I).obj V)) F

private theorem lowerComparison_sections {X Y : Scheme.{u}} (b : X ⟶ Y)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (W : Y.ProEtᵒᵖ) (m : N.X.obj.obj ((siteMap b).op.obj W)) :
    (((lowerComparison Λ b).hom.app N).val.app W).hom m = m :=
  (lowerComparison_existsUnique Λ b).exists.choose_spec N W m

private theorem internalHom_smul {X Y : Scheme.{u}} (b : X ⟶ Y)
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : F ⟶ (CondensedRing.lowerStar Λ b).obj N)
    (W : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj W)
    (x : ((equivalence Λ Y).functor.obj F).val.obj W) :
    (f.hom.hom.app W)
        (r • x) =
      (ModuleCat.smul
        (((equivalence Λ X).functor.obj N).val.obj
          ((siteMap b).op.obj W)) (((coefficientMap Λ b).hom.app W).hom r)).hom
        ((f.hom.hom.app W) x) := by
  let eta := (equivalence Λ (Y)).functor.map
    f ≫
      (lowerComparison Λ b).hom.app N
  have h := (eta.val.app W).hom.map_smul r x
  change (((lowerComparison Λ b).hom.app N).val.app W).hom
      ((f.hom.hom.app W) (r • x)) =
    (ModuleCat.smul (((equivalence Λ (X)).functor.obj N).val.obj
        ((siteMap b).op.obj W)) (((coefficientMap Λ b).hom.app W).hom r)).hom
      ((((lowerComparison Λ b).hom.app N).val.app W).hom
        ((f.hom.hom.app W) x)) at h
  have hd0 := lowerComparison_sections Λ b N W
    ((f.hom.hom.app W) (r • x))
  have hd1 := lowerComparison_sections Λ b N W
    ((f.hom.hom.app W) x)
  have hlin := hd0.symm.trans (h.trans (congrArg
    (fun m ↦ (ModuleCat.smul
      (((equivalence Λ (X)).functor.obj N).val.obj
        ((siteMap b).op.obj W)) (((coefficientMap Λ b).hom.app W).hom r)).hom m) hd1))
  exact hlin

private theorem internalHomRestriction_smul {X Y : Scheme.{u}} (b : X ⟶ Y)
    (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : F ⟶ (CondensedRing.lowerStar Λ b).obj N)
    (W : Y.ProEt) (V : X.ProEt) (g : V ⟶ (siteMap b).obj W)
    (r : (ring Λ Y).obj.obj (op W))
    (x : ((equivalence Λ Y).functor.obj F).val.obj (op W)) :
    N.X.obj.map g.op (f.hom.hom.app (op W) (r • x)) =
      (ModuleCat.smul (((equivalence Λ X).functor.obj N).val.obj (op V))
        ((ring Λ X).obj.map g.op (((coefficientMap Λ b).hom.app (op W)).hom r))).hom
        (N.X.obj.map g.op (f.hom.hom.app (op W) x)) := by
  have hs := PresheafOfModules.map_smul
    (((equivalence Λ X).functor.obj N).val) g.op
    (((coefficientMap Λ b).hom.app (op W)).hom r) (f.hom.hom.app (op W) x)
  exact (congrArg (fun m ↦ N.X.obj.map g.op m)
    (internalHom_smul Λ b F N f (op W) r x)).trans hs

private theorem unitSection_smul (A : Type u) [CommRing A] (I : Ideal A)
    (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A))))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (r : (ring Λ (Spec (.of A))).obj.obj
      (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))))
    (x : ((equivalence Λ (Spec (.of A))).functor.obj F).val.obj
      (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)))) :
    unitSection Λ A I F V (r • x) =
      (ModuleCat.smul
        (((equivalence Λ (Spec (.of (A ⧸ I)))).functor.obj
          ((CondensedRing.upperStar Λ (immersion A I)).obj F)).val.obj
            (op ((AffineProEt.toProEt _).obj V)))
        (scalarSection Λ A I V r)).hom (unitSection Λ A I F V x) := by
  exact internalHomRestriction_smul Λ (immersion A I) F
    ((CondensedRing.upperStar Λ (immersion A I)).obj F)
    ((CondensedRing.upperStarLowerStarAdjunction Λ (immersion A I)).unit.app F)
    ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))
    ((AffineProEt.toProEt _).obj V) (fiberIso A I V).hom r x

private theorem equivalence_exact
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ≌ D) (hE : E.functor.Additive) (hInv : E.inverse.Additive) :
    ∃ (_hE : E.functor.Additive) (_hInv : E.inverse.Additive),
      E.functor.PreservesHomology ∧ E.inverse.PreservesHomology ∧
      (E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).PreservesHomology ∧
      (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).PreservesHomology ∧
      E.functor.PreservesKInjectiveComplexes ∧ E.inverse.PreservesKInjectiveComplexes ∧
      (∀ (K L : CochainComplex C ℤ) (f : K ⟶ L), QuasiIso f →
        QuasiIso ((E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
  have := hE
  have := hInv
  refine ⟨hE, hInv, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  intro K L f hf
  have := hf
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f _

attribute [local semireducible] CondensedRing.upperStar
  CondensedRing.upperStarLowerStarAdjunction fiberIso closedSiteLift closedSiteBaseChange
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] closedComparison abelianBasisComparison

/-- Internal normalization, exact test evaluation, and the closed-evaluation inverse
of the actual module unit. The existential comparison is fixed by its displayed equation
with the sheafification unit, so no unrelated section isomorphism is substituted.

Source: Stacks 09BK, 09BL (1)--(2), 03D2, 03D3, 03D6, 03D7 and 08BJ
(blueprint: lem-sfb-closed-test-unit-evaluation).

Proof:
1. The recorded additive equivalences preserve homology, termwise homology and
   K-injectives. Preservation of homology gives preservation of quasi-isomorphisms.
2. The extension/restriction-of-scalars comparison identifies internal inverse image
   with abelian inverse image. Its extension-unit equation identifies the actual units.
   The forgotten ordinary module unit has an invertible abelian adjunct; composing
   its inverse with the internal comparison gives q and its inverseSection equation.
   The recorded operation transport supplies the section-module unit/counit equations.
3. Geometric weak contractibility gives surjectivity of full-site epimorphisms.
   The existing affine-basis restriction equivalence transfers it to the basis,
   including the identity test over the lifted scheme.
4. Weakly contractible module evaluation preserves homology. Compose it with the
   section-module equivalence and the exact forgetful functor to abelian groups.
5. Closed-lift geometry supplies the closed pullback and specialization assertions.
   Transport specialization into the global-section quotient coordinates and apply
   the closed-site counit theorem to the local identity test.
6. The abelian specialization theorem makes the actual abelian unit invertible on
   the lifted test. The internal comparison and fibre restriction give bijectivity
   of unitSection. Apply the section-module equivalence and the identity-on-sections
   direct-image comparison to its internal unit; linearity and semilinear restriction
   give exactly the scalarSection formula.
7. Sheafified precomposition by the lift is left adjoint to basis base change.
   The inverse mate of the identity square of right adjoints under the two basis
   equivalences is invertible. Its unit equation, the precomposition adjunction and
   the sheafification unit identify its section map with the actual abelian unit
   restricted along the fibre isomorphism. Compose with the internal comparison to
   obtain c. Its equation and bijectivity identify its inverse with closed evaluation.
   Naturality of c and the sheafification unit proves both naturality assertions.
-/
theorem closed_test_unit_evaluation :
    (∀ T : Scheme.{u},
      ∃ (_hE : (equivalence Λ T).functor.Additive)
        (_hInv : (equivalence Λ T).inverse.Additive),
      (equivalence Λ T).functor.PreservesHomology ∧
      (equivalence Λ T).inverse.PreservesHomology ∧
      ((equivalence Λ T).functor.mapHomologicalComplex (ComplexShape.up ℤ)).PreservesHomology ∧
      ((equivalence Λ T).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).PreservesHomology ∧
      (equivalence Λ T).functor.PreservesKInjectiveComplexes ∧
      (equivalence Λ T).inverse.PreservesKInjectiveComplexes ∧
      (∀ (K L : CochainComplex
          (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
        (f : K ⟶ L), QuasiIso f →
          QuasiIso
            (((equivalence Λ T).functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f))) ∧
    (∀ {X Y : Scheme.{u}} (b : X ⟶ Y),
      (CondensedRing.upperStar Λ b).PreservesHomology ∧
      Nonempty (CondensedRing.upperStar Λ b ⋙ Mod.forget (condensedRingObj Λ X) ≅
        Mod.forget (condensedRingObj Λ Y) ⋙ ProEtale.upperStar Ab.{u + 1} b) ∧
      (∃ q : (equivalence Λ Y).functor ⋙
          ProEtaleTensorComparison.inverse b
            (sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology Y) (condensedRingObj Λ Y)) ⋙
          SheafOfModules.toSheaf.{u + 1} ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ProEtaleTensorComparison.inverseRing b
              (sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology Y) (condensedRingObj Λ Y)))) ≅
          CondensedRing.upperStar Λ b ⋙ Mod.forget (condensedRingObj Λ X),
        ∀ (F : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
          (W : Y.ProEt) (x : F.X.obj.obj (op W)),
          ((q.hom.app F).hom.app (op ((siteMap b).obj W)))
              (ProEtaleTensorComparison.inverseSection b
                ((equivalence Λ Y).functor.obj F) W x) =
            (((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app F).hom.hom.app
              (op W)) x) ∧
      (∀ M,
        (equivalence Λ Y).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ b).unit.app M) ≫
          (lowerComparison Λ b).hom.app ((CondensedRing.upperStar Λ b).obj M) ≫
          (InternalModuleOperations.lowerStar Λ b).map ((upperComparison Λ b).hom.app M) =
        (adjunction Λ b).unit.app ((equivalence Λ Y).functor.obj M)) ∧
      (∀ N,
        (InternalModuleOperations.upperStar Λ b).map ((lowerComparison Λ b).inv.app N) ≫
          (upperComparison Λ b).inv.app ((CondensedRing.lowerStar Λ b).obj N) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ b).counit.app N) =
        (adjunction Λ b).counit.app ((equivalence Λ X).functor.obj N)) ∧
      (∀ (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
        (W : Y.ProEt),
        ((CondensedRing.lowerStar Λ b).obj N).X.obj.obj (op W) =
          N.X.obj.obj (op ((siteMap b).obj W)))) ∧
    (∀ (A : Type u) [CommRing A] (I : Ideal A),
      ∃ c : liftSections Λ A I ⋙ presheafToSheaf
          (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1} ≅ inverseBasis Λ A I,
      (∀ (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of A))))
        (V : (Spec (.of (A ⧸ I))).AffineProEt)
        (x : ((liftSections Λ A I).obj F).obj (op V)),
        ((c.hom.app F).hom.app (op V))
            (((toSheafify (topology (Spec (.of (A ⧸ I))))
              ((liftSections Λ A I).obj F)).app (op V)) x) =
          unitSection Λ A I F V x) ∧
      (∀ (V : (Spec (.of (A ⧸ I))).AffineProEt)
        [IsWContractibleRing Γ(V.left, ⊤)]
        [IsWContractibleRing Γ(((closedSiteLift A I).obj V).left, ⊤)],
        (∀ (P Q : Sheaf (ProEt.topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) (f : P ⟶ Q),
          Epi f → Function.Surjective (f.hom.app (op ((AffineProEt.toProEt _).obj V)))) ∧
        (∀ (P Q : Sheaf (ProEt.topology (Spec (.of A))) (Type (u + 1))) (f : P ⟶ Q),
          Epi f → Function.Surjective
            (f.hom.app (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))))) ∧
        (∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) (f : P ⟶ Q),
          Epi f → Function.Surjective (f.hom.app (op V))) ∧
        (∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (u + 1))) (f : P ⟶ Q),
          Epi f → Function.Surjective (f.hom.app (op ((closedSiteLift A I).obj V)))) ∧
        (∀ (P Q : Sheaf (topology (((closedSiteLift A I).obj V).left))
            (Type (u + 1))) (f : P ⟶ Q),
          Epi f → Function.Surjective
            (f.hom.app (op (AffineProEt.mk (𝟙 ((closedSiteLift A I).obj V).left)
              (proAffineEtale.of_isAffine _))))) ∧
        (SheafOfModules.evaluation (ring Λ (Spec (.of A)))
          (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)))).PreservesHomology ∧
        (SheafOfModules.evaluation (ring Λ (Spec (.of (A ⧸ I))))
          (op ((AffineProEt.toProEt _).obj V))).PreservesHomology ∧
        (Mod.forget (condensedRingObj Λ (Spec (.of A))) ⋙
          sheafToPresheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1} ⋙
          (CategoryTheory.evaluation _ _).obj
            (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)))).PreservesHomology ∧
        (Mod.forget (condensedRingObj Λ (Spec (.of (A ⧸ I)))) ⋙
          sheafToPresheaf (ProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1} ⋙
          (CategoryTheory.evaluation _ _).obj
            (op ((AffineProEt.toProEt _).obj V))).PreservesHomology ∧
        IsClosedImmersion (closedSiteLiftInclusion A I V) ∧
        IsPullback (closedSiteLiftInclusion A I V) V.hom
          ((closedSiteLift A I).obj V).hom (immersion A I) ∧
        (∀ x : ((closedSiteLift A I).obj V).left,
          ∃ z : V.left, Specializes x ((closedSiteLiftInclusion A I V) z)) ∧
        (∀ adj : closedSiteLift (Γ(((closedSiteLift A I).obj V).left, ⊤))
            (RingHom.ker (closedSiteLiftInclusion A I V).appTop.hom) ⊣
          closedSiteBaseChange (Γ(((closedSiteLift A I).obj V).left, ⊤))
            (RingHom.ker (closedSiteLiftInclusion A I V).appTop.hom),
          IsIso (adj.counit.app (AffineProEt.mk (𝟙 _) (proAffineEtale.of_isAffine _)))) ∧
        (∀ F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
            (condensedRingObj Λ (Spec (.of A))),
          ∃ e : ((liftSections Λ A I).obj F).obj (op V) ≃+
              ((inverseBasis Λ A I).obj F).obj.obj (op V),
            (∀ x, e x = unitSection Λ A I F V x) ∧
            (∀ (r : (ring Λ (Spec (.of A))).obj.obj
                (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V))))
              (x : ((equivalence Λ (Spec (.of A))).functor.obj F).val.obj
                (op ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)))),
              unitSection Λ A I F V (r • x) =
                (ModuleCat.smul
                  (((equivalence Λ (Spec (.of (A ⧸ I)))).functor.obj
                    ((CondensedRing.upperStar Λ (immersion A I)).obj F)).val.obj
                      (op ((AffineProEt.toProEt _).obj V)))
                  (scalarSection Λ A I V r)).hom (unitSection Λ A I F V x)) ∧
            (∀ y, ((toSheafify (topology (Spec (.of (A ⧸ I))))
                ((liftSections Λ A I).obj F)).app (op V)) (e.symm y) =
              ((c.inv.app F).hom.app (op V)) y))) ∧
      (∀ (F G : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of A)))) (f : F ⟶ G)
        (V : (Spec (.of (A ⧸ I))).AffineProEt)
        [IsWContractibleRing Γ(V.left, ⊤)]
        [IsWContractibleRing Γ(((closedSiteLift A I).obj V).left, ⊤)]
        (x : ((liftSections Λ A I).obj F).obj (op V)),
        (((inverseBasis Λ A I).map f).hom.app (op V)) (unitSection Λ A I F V x) =
          unitSection Λ A I G V (((liftSections Λ A I).map f).app (op V) x)) ∧
      (∀ (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of A))))
        (V W : (Spec (.of (A ⧸ I))).AffineProEt)
        [IsWContractibleRing Γ(V.left, ⊤)]
        [IsWContractibleRing Γ(((closedSiteLift A I).obj V).left, ⊤)]
        [IsWContractibleRing Γ(W.left, ⊤)]
        [IsWContractibleRing Γ(((closedSiteLift A I).obj W).left, ⊤)]
        (a : V ⟶ W) (x : ((liftSections Λ A I).obj F).obj (op W)),
        ((inverseBasis Λ A I).obj F).obj.map a.op (unitSection Λ A I F W x) =
          unitSection Λ A I F V (((liftSections Λ A I).obj F).map a.op x))) := by
  classical
  constructor
  · intro T
    exact equivalence_exact (equivalence Λ T)
      (((internal_module_operations_transport Λ).1 T).1)
      (((internal_module_operations_transport Λ).1 T).2.1)
  constructor
  · intro X Y b
    refine ⟨inferInstance, ?_, ?_,
      (internal_module_operations_transport Λ).2.1 b |>.2.1,
      (internal_module_operations_transport Λ).2.1 b |>.2.2, ?_⟩
    · exact ⟨underlyingPullbackIso Λ b⟩
    · let R := sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology Y) (condensedRingObj Λ Y)
      have := ordinaryUnderlyingComparison_isIso b R
      let o := asIso (ordinaryUnderlyingComparison b R)
      let q := Functor.isoWhiskerLeft (equivalence Λ Y).functor o.symm ≪≫
        (underlyingPullbackIso Λ b).symm
      refine ⟨q, ?_⟩
      intro F W x
      let M := (equivalence Λ Y).functor.obj F
      have ho' := (ordinaryUnderlyingComparison_unit b R M W x).symm
      have he := Iso.hom_inv_id_apply
        (((sheafSections (ProEt.topology X) Ab.{u + 1}).obj
          (op ((siteMap b).obj W))).mapIso (o.app M))
        (((proEtaleSheafAdjunction b Ab.{u + 1}).unit.app F.X).hom.app (op W) x)
      change (o.inv.app M).hom.app _ ((o.hom.app M).hom.app _ _) = _ at he
      have hunit := congrArg (fun g ↦ g.hom.app (op W) x)
        (underlyingPullbackIso_inv_unit Λ b F)
      calc
        _ = ((underlyingPullbackIso Λ b).inv.app F).hom.app
            (op ((siteMap b).obj W)) ((o.inv.app M).hom.app
              (op ((siteMap b).obj W))
                (ProEtaleTensorComparison.inverseSection b M W x)) := by rfl
        _ = ((underlyingPullbackIso Λ b).inv.app F).hom.app _
            ((o.inv.app M).hom.app _ ((o.hom.app M).hom.app _
              (((proEtaleSheafAdjunction b Ab.{u + 1}).unit.app F.X).hom.app
                (op W) x))) := congrArg
          (fun z ↦ ((underlyingPullbackIso Λ b).inv.app F).hom.app _
            ((o.inv.app M).hom.app _ z)) ho'
        _ = _ := (congrArg
          (fun z ↦ ((underlyingPullbackIso Λ b).inv.app F).hom.app _ z) he).trans hunit
    · intro N W
      rfl
  · intro A hA I
    let c := closedComparison Λ A I
    have hc : ∀ (F : Mod (Sheaf (ProEt.topology (Spec (.of A))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of A))))
        (V : (Spec (.of (A ⧸ I))).AffineProEt)
        (x : ((liftSections Λ A I).obj F).obj (op V)),
        ((c.hom.app F).hom.app (op V))
          (((toSheafify (topology (Spec (.of (A ⧸ I))))
            ((liftSections Λ A I).obj F)).app (op V)) x) =
          unitSection Λ A I F V x := closedComparison_unit Λ A I
    clear_value c
    refine ⟨c, hc, ?_, ?_, ?_⟩
    · intro V hV hB
      have hz := full_test_surjective (Spec (.of (A ⧸ I))) V
      have hb := full_test_surjective (Spec (.of A)) ((closedSiteLift A I).obj V)
      have hz' := basis_test_surjective (Spec (.of (A ⧸ I))) V
      have hb' := basis_test_surjective (Spec (.of A)) ((closedSiteLift A I).obj V)
      let : IsWContractibleRing Γ((AffineProEt.mk
          (𝟙 ((closedSiteLift A I).obj V).left)
          (proAffineEtale.of_isAffine _)).left, ⊤) := hB
      have hId := basis_test_surjective (((closedSiteLift A I).obj V).left)
        (AffineProEt.mk (𝟙 _) (proAffineEtale.of_isAffine _))
      have heU := ProEt.weaklyContractible_evaluation_preservesHomology (Spec (.of A))
        (sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology (Spec (.of A)))
          (condensedRingObj Λ (Spec (.of A))))
        ((AffineProEt.toProEt _).obj ((closedSiteLift A I).obj V)) hb
      have heZ := ProEt.weaklyContractible_evaluation_preservesHomology (Spec (.of (A ⧸ I)))
        (sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology (Spec (.of (A ⧸ I))))
          (condensedRingObj Λ (Spec (.of (A ⧸ I)))))
        ((AffineProEt.toProEt _).obj V) hz
      have hi := ((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).1
      have hp := ((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.1
      have hs := ((affine_closed_site_functor_properties A I).2.2.2.2.2.2.2 V).2.2
      refine ⟨hz, hb, hz', hb', hId, heU, heZ,
        internal_test_preservesHomology Λ _ _, internal_test_preservesHomology Λ _ _,
        hi, hp, hs, local_test_counit A I V, ?_⟩
      intro F
      let e := AddEquiv.ofBijective (unitSection Λ A I F V)
        (unitSection_bijective Λ A I F V)
      refine ⟨e, (fun _ ↦ rfl), unitSection_smul Λ A I F V, ?_⟩
      intro y
      apply (ConcreteCategory.bijective_of_isIso ((c.hom.app F).hom.app (op V))).injective
      rw [hc]
      change e (e.symm y) = _
      exact (e.apply_symm_apply y).trans
        (Iso.inv_hom_id_apply
          (((sheafSections (topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}).obj (op V)).mapIso
            (c.app F)) y).symm
    · intro F G f V _ _ x
      rw [← hc F V x, ← hc G V]
      have h := congrArg (fun g ↦ g.hom.app (op V)
        (((toSheafify (topology (Spec (.of (A ⧸ I))))
          ((liftSections Λ A I).obj F)).app (op V)) x)) (c.hom.naturality f)
      change _ = _ at h
      erw [← h]
      exact congrArg (((c.hom.app G).hom.app (op V)))
        (congrArg (fun g ↦ g.app (op V) x)
          (toSheafify_naturality (topology (Spec (.of (A ⧸ I))))
            ((liftSections Λ A I).map f))).symm
    · intro F V W _ _ _ _ a x
      rw [← hc F W x, ← hc F V]
      erw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      rfl

end AlgebraicGeometry.ProEtale.ClosedTest
