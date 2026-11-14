/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Projection arrows on the original small pro-etale sites

Source: proper base change, definition 1264.
This repairs only the site-universe interface and reexports the existing general arrows.
The inverse is the localization of the specified finite-total chain inverse.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

section UnitNormalization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem proEtaleTensorPair_tensorHom
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M M' N N' : proEtaleRingModules X R} (v : M ⟶ M') (w : N ⟶ N')
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((SheafOfModules.monoidalCategory R).tensorHom v w).val.app U
        (proEtaleTensorPair X R M N U x y) =
      proEtaleTensorPair X R M' N' U (v.val.app U x) (w.val.app U y) := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let G : proEtaleRingModules X R ⥤ PresheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj :=
    SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)
  let : G.LaxMonoidal := adj.rightAdjointLaxMonoidal
  exact (congrArg (fun φ ↦ φ.app U (x ⊗ₜ[R.obj.obj U] y))
    (Functor.LaxMonoidal.μ_natural G v w)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem proEtaleTensorPair_rightUnitor
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (r : R.obj.obj U) :
    ((SheafOfModules.monoidalCategory R).rightUnitor M).hom.val.app U
        (proEtaleTensorPair X R M (SheafOfModules.unit _) U x r) = r • x := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let T := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  have h : (SheafOfModules.tensorObjIsoSheafification M (SheafOfModules.unit _)).inv ≫
      (ρ_ M).hom = T.map (ρ_ M.val).hom ≫ adj.counit.app M := by
    simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_inv,
      Functor.Monoidal.μIso_inv, Iso.symm_inv, tensorIso_hom, Iso.app_hom, asIso_hom]
    change Functor.OplaxMonoidal.δ T M.val (𝟙_ _) ≫
      (adj.counit.app M ⊗ₘ Functor.OplaxMonoidal.η T) ≫ (ρ_ M).hom = _
    rw [Functor.OplaxMonoidal.δ_comp_tensorHom_η_assoc]
    rw [rightUnitor_naturality, Iso.inv_hom_id_assoc]
  have he := congrArg (fun z ↦ z.val.app U
    ((adj.unit.app (M.val ⊗ (SheafOfModules.unit _).val)).app U
      (x ⊗ₜ[R.obj.obj U] r))) h
  have hn := congrArg (fun z ↦ z.app U (x ⊗ₜ[R.obj.obj U] r))
    (adj.unit.naturality ((ρ_ M.val).hom))
  have ht := congrArg (fun z ↦ z.app U (r • x)) (adj.right_triangle_components M)
  change (adj.unit.app M.val).app U (r • x) =
    (T.map (ρ_ M.val).hom).val.app U
      ((adj.unit.app (M.val ⊗ (SheafOfModules.unit _).val)).app U
        (x ⊗ₜ[R.obj.obj U] r)) at hn
  change (adj.counit.app M).val.app U ((adj.unit.app M.val).app U (r • x)) =
    r • x at ht
  exact he.trans ((congrArg (fun z ↦ (adj.counit.app M).val.app U z) hn.symm).trans ht)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem proEtaleTensorPair_hom_ext
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N H : proEtaleRingModules X R)
    (v w : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H)
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      v.val.app U (proEtaleTensorPair X R M N U x y) =
        w.val.app U (proEtaleTensorPair X R M N U x y)) : v = w := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change v.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U t)) =
    w.val.app U ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U t))
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add t s ht hs => simp only [map_add, ht, hs]

end UnitNormalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

section ProjectionUnitProof

attribute [local irreducible] proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Unit normalization of the canonical ordinary comparison on the original site.
Source: definition 1264, ordinary finite-free identification. -/
theorem proEtaleProjectionUnit_existsUnique :
    ∃! j : (proEtaleRingModulePullback f R S c).obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
        SheafOfModules.unit ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S),
      ∀ M : proEtaleRingModules Y R,
        (proEtaleOrdinaryTensorPullback f R S c M
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))).hom ≫
          (SheafOfModules.monoidalCategory S).tensorHom
            (𝟙 ((proEtaleRingModulePullback f R S c).obj M)) j.hom ≫
          ((SheafOfModules.monoidalCategory S).rightUnitor
            ((proEtaleRingModulePullback f R S c).obj M)).hom =
        (proEtaleRingModulePullback f R S c).map
          (((SheafOfModules.monoidalCategory R).rightUnitor M).hom) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let adj := proEtaleRingModuleAdjunction f R S c
  let φ : (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let e := adj.leftAdjointUniq adj'
  let j := e.app (SheafOfModules.unit _) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have hj : adj.homEquiv _ _ j.hom = SheafOfModules.unitToPushforwardObjUnit φ := by
    change adj.homEquiv _ _ (e.hom.app _ ≫ _) = _
    rw [adj.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  have hcompat (M : proEtaleRingModules Y R) :
      (proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom ≫
        (𝟙 _ ⊗ₘ j.hom) ≫ (ρ_ _).hom =
      (proEtaleRingModulePullback f R S c).map (ρ_ M).hom := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, adj.unit_naturality]
    apply proEtaleTensorPair_hom_ext Y R
    intro U m r
    obtain ⟨U⟩ := U
    have hmu := (Classical.choose_spec
      (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).2 M (𝟙_ _) U m r
    have hjr := congrArg (fun z ↦ z.val.app (Opposite.op U) r) hj
    rw [Adjunction.homEquiv_unit] at hjr
    change j.hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
      ((adj.unit.app (𝟙_ _)).val.app (Opposite.op U) r) =
        (proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r at hjr
    change (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app _
        (((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app _
          ((proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom.val.app _
            ((adj.unit.app _).val.app _ (proEtaleTensorPair Y R M (𝟙_ _) _ m r)))) =
      (adj.unit.app M).val.app _ ((ρ_ M).hom.val.app _
        (proEtaleTensorPair Y R M (𝟙_ _) _ m r))
    erw [hmu]
    let V := Opposite.op ((proEtaleBaseChange f).obj U)
    let m' : ((proEtaleRingModulePullback f R S c).obj M).val.obj V :=
      (adj.unit.app M).val.app (Opposite.op U) m
    let r' : ((proEtaleRingModulePullback f R S c).obj (𝟙_ _)).val.obj V :=
      (adj.unit.app (𝟙_ _)).val.app (Opposite.op U) r
    change j.hom.val.app V r' =
      (proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r at hjr
    change (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V
        (((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app V
          (proEtaleTensorPair X S _ _ V m' r')) = _
    have htens := proEtaleTensorPair_tensorHom X S
      (𝟙 ((proEtaleRingModulePullback f R S c).obj M)) j.hom V m' r'
    change ((SheafOfModules.monoidalCategory S).tensorHom (𝟙 _) j.hom).val.app V
        (proEtaleTensorPair X S _ _ V m' r') =
      proEtaleTensorPair X S _ _ V m' (j.hom.val.app V r') at htens
    calc
      _ = (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V
          (proEtaleTensorPair X S _ _ V m' (j.hom.val.app V r')) :=
        congrArg (fun z ↦
          (ρ_ ((proEtaleRingModulePullback f R S c).obj M)).hom.val.app V z) htens
      _ = (show S.obj.obj V from j.hom.val.app V r') • m' :=
        proEtaleTensorPair_rightUnitor X S _ V m' (j.hom.val.app V r')
      _ = ((proEtaleRingDirectImageMap f R S c).hom.app (Opposite.op U) r) • m' :=
        congrArg (fun z ↦ z • m') hjr
      _ = (adj.unit.app M).val.app (Opposite.op U)
          ((show R.obj.obj (Opposite.op U) from r) • m) :=
        ((adj.unit.app M).val.app (Opposite.op U)).hom.map_smul r m |>.symm
      _ = _ := congrArg (fun z ↦ (adj.unit.app M).val.app (Opposite.op U) z)
        (proEtaleTensorPair_rightUnitor Y R M (Opposite.op U) m r).symm
  refine ⟨j, hcompat, ?_⟩
  intro j' hj'
  apply Iso.ext
  have h := (hj' (𝟙_ _)).trans (hcompat (𝟙_ _)).symm
  let T := (proEtaleRingModulePullback f R S c).obj (𝟙_ _)
  have ht : (𝟙 T ⊗ₘ j'.hom) = (𝟙 T ⊗ₘ j.hom) :=
    (cancel_mono (ρ_ T).hom).1
      ((cancel_epi (proEtaleOrdinaryTensorPullback f R S c (𝟙_ _) (𝟙_ _)).hom).1 h)
  have h' := congrArg (fun z ↦ (j.inv ⊗ₘ 𝟙 _) ≫ z) ht
  simp only [tensorHom_comp_tensorHom, Category.id_comp] at h'
  have h'' := congrArg (fun z ↦ (λ_ _).inv ≫ z) h'
  rw [leftUnitor_inv_comp_tensorHom, leftUnitor_inv_comp_tensorHom] at h''
  exact (cancel_mono ((λ_ (𝟙_ (proEtaleRingModules X S))).inv ≫
    j.inv ▷ (𝟙_ (proEtaleRingModules X S)))).1 h''

end ProjectionUnitProof

set_option backward.isDefEq.respectTransparency false in
/-- Bounded split-free coefficients are flat and K-flat on the original site.
Source: definition 1264, representatives C and J. -/
theorem proEtaleStrictPerfect_flat
    (F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (P : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
    (hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) :
    proEtaleFlatRepresentatives Y R F := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  have (M : proEtaleRingModules Y R) :
      PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  let := SheafOfModules.symmetricCategory R
  have (M : proEtaleRingModules Y R) :
      PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ : GradedObject ℤ (proEtaleRingModules Y R),
      GradedObject.HasTensor X₁ X₂ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ (proEtaleRingModules Y R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ (proEtaleRingModules Y R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (proEtaleRingModules Y R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have hflat (n : ℤ) : SheafOfModules.IsFlatOnSite (J := ProEt.topology Y)
      (R := R) (F.X n) := by
    have hfree : ObjectProperty.flat
        (∏ᶜ fun _ : Fin (P.N n) ↦ 𝟙_ (proEtaleRingModules Y R)) := by
      exact ObjectProperty.flat.prop_pi _ (fun _ ↦ ObjectProperty.prop_unit _)
    have ht : ObjectProperty.flat (F.X n) :=
      ObjectProperty.prop_of_retract _ ⟨P.i n, P.p n, P.splitting n⟩ hfree
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (F.X n)).symm ht.2
  refine ⟨?_, hflat⟩
  obtain ⟨a, b, hb⟩ := hb
  have : F.IsStrictlyLE (b + 1) :=
    (F.isStrictlyLE_iff _).2 (fun n hn ↦ hb n (Or.inr (by omega)))
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R F (b + 1) hflat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The resolution comparison elaborates several large total-tensor naturality squares.
/-- Mixed tensor representatives, normalized at every flat K-flat resolution. -/
theorem proEtaleMixedTensor_existsUnique (a : ProEtaleTensorModel Y R)
    (A F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hf : proEtaleFlatRepresentatives Y R F) :
    ∃! z : a.tensor.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj F) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor A F (proEtaleOrdinaryTensor Y R)),
      ∀ (P : CochainComplex (proEtaleRingModules Y R) ℤ)
        (hp : proEtaleFlatRepresentatives Y R P) (p : P ⟶ A), QuasiIso p →
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj F))) ≫ z.hom =
        a.representative.inv.app (⟨P, hp⟩, ⟨F, hf⟩) ≫
          DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap p (𝟙 F)
            (proEtaleOrdinaryTensor Y R) (ComplexShape.up ℤ)) := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  let := SheafOfModules.monoidalPreadditive_kfg R
  let := SheafOfModules.isGrothendieckAbelian_kfg R
  let := SheafOfModules.hasFunctorialFlatResolution_kfg R
  let M := proEtaleRingModules Y R
  let : Zero (CochainComplex M ℤ) := HasZeroObject.zero' (CochainComplex M ℤ)
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ M))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ M).essImage ≤ ObjectProperty.flat :=
    ObjectProperty.flat.essImage_ι_le
  have hres (K : CochainComplex M ℤ) :
      proEtaleFlatRepresentatives Y R (Λ.resolutionFunctor.obj K) := by
    have hk := Λ.kFlat_resolutionFunctor_obj hι K
    have hflat (n : ℤ) : ObjectProperty.flat ((Λ.resolutionFunctor.obj K).X n) := by
      have := CochainComplex.closedUnderColimitsOfShape_flat M ℤ
      let c := Λ.colimitOfShapeResolutionFunctorObj K
      exact ObjectProperty.prop_of_isColimit _
        (isColimitOfPreserves (HomologicalComplex.eval M (.up ℤ) n) c.isColimit)
        (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
    refine ⟨?_, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm (hflat n).2⟩
    intro Z hZ
    let T := MonoidalCategory.tensorRight (Λ.resolutionFunctor.obj K)
    have hz : QuasiIso (0 : (0 : CochainComplex M ℤ) ⟶ Z) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
    have hmap : QuasiIso (T.map (0 : (0 : CochainComplex M ℤ) ⟶ Z)) := hk.2 _ hz
    have htzero : (T.obj (0 : CochainComplex M ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (T.map (0 : (0 : CochainComplex M ℤ) ⟶ Z)) i).1 (htzero i)
  have htensor {K K' : CochainComplex M ℤ} (p : K ⟶ K') (hp : QuasiIso p) :
      QuasiIso (HomologicalComplex.mapBifunctorMap p (𝟙 F)
        (proEtaleOrdinaryTensor Y R) (.up ℤ)) := by
    have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic p).1 hp
    have ht := hf.1 (CochainComplex.mappingCone p) hc
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    intro i
    exact (ht i).of_iso
      (CochainComplex.mapBifunctorMappingCone₁Iso p F (proEtaleOrdinaryTensor Y R))
  let q := Λ.resolutionNatTrans
  let PA := Λ.resolutionFunctor.obj A
  have hqA : QuasiIso (q.app A) := inferInstance
  have hqp : IsIso (DerivedCategory.Q.{u + 2}.map (q.app A)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hqA
  have hqt : IsIso (DerivedCategory.Q.{u + 2}.map
      (HomologicalComplex.mapBifunctorMap (q.app A) (𝟙 F)
        (proEtaleOrdinaryTensor Y R) (.up ℤ))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact htensor _ hqA
  let : IsIso (Prod.mkHom (DerivedCategory.Q.{u + 2}.map (q.app A))
    (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) :=
      (Iso.prod (asIso (DerivedCategory.Q.{u + 2}.map (q.app A)))
      (Iso.refl (DerivedCategory.Q.{u + 2}.obj F))).isIso_hom
  let e := a.tensor.mapIso
    (Iso.prod (asIso (DerivedCategory.Q.{u + 2}.map (q.app A)))
      (Iso.refl (DerivedCategory.Q.{u + 2}.obj F)))
  let z := e.symm ≪≫ (a.representative.app (⟨PA, hres A⟩, ⟨F, hf⟩)).symm ≪≫
    asIso (DerivedCategory.Q.{u + 2}.map (HomologicalComplex.mapBifunctorMap (q.app A) (𝟙 F)
      (proEtaleOrdinaryTensor Y R) (.up ℤ)))
  refine ⟨z, ?_, ?_⟩
  · intro P hp p hq
    have hqP : QuasiIso (q.app P) := inferInstance
    have : IsIso (DerivedCategory.Q.{u + 2}.map (q.app P)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact hqP
    let : IsIso (Prod.mkHom (DerivedCategory.Q.{u + 2}.map (q.app P))
      (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) :=
        (Iso.prod (asIso (DerivedCategory.Q.{u + 2}.map (q.app P)))
        (Iso.refl (DerivedCategory.Q.{u + 2}.obj F))).isIso_hom
    apply (cancel_epi (a.tensor.map (Prod.mkHom (DerivedCategory.Q.{u + 2}.map (q.app P))
      (𝟙 (DerivedCategory.Q.{u + 2}.obj F))))).1
    let T := ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj F
    have hn : a.tensor.map (Prod.mkHom
        (DerivedCategory.Q.{u + 2}.map (Λ.resolutionFunctor.map p))
        (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) ≫
        a.representative.inv.app (⟨_, hres A⟩, ⟨F, hf⟩) =
      a.representative.inv.app (⟨_, hres P⟩, ⟨F, hf⟩) ≫
        DerivedCategory.Q.{u + 2}.map (T.map (Λ.resolutionFunctor.map p)) := by
      have h := a.representative.inv.naturality
        (Prod.mkHom (ObjectProperty.homMk (X := ⟨_, hres P⟩) (Y := ⟨_, hres A⟩)
          (Λ.resolutionFunctor.map p))
          (𝟙 (⟨F, hf⟩ : (proEtaleFlatRepresentatives Y R).FullSubcategory)))
      simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
        ObjectProperty.ι_obj, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
        ObjectProperty.FullSubcategory.id_hom, Functor.uncurry_obj_map] at h
      erw [DerivedCategory.Q.{u + 2}.map_id F,
        (((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)).obj (Λ.resolutionFunctor.obj A)).map_id F,
        Category.comp_id] at h
      simpa only [T, Functor.flip_obj_map] using h
    have hn' : a.tensor.map (Prod.mkHom
        (DerivedCategory.Q.{u + 2}.map (q.app P))
        (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) ≫
        a.representative.inv.app (⟨P, hp⟩, ⟨F, hf⟩) =
      a.representative.inv.app (⟨_, hres P⟩, ⟨F, hf⟩) ≫
        DerivedCategory.Q.{u + 2}.map (T.map (q.app P)) := by
      have h := a.representative.inv.naturality
        (Prod.mkHom (ObjectProperty.homMk (X := ⟨_, hres P⟩) (Y := ⟨_, hp⟩)
          (q.app P))
          (𝟙 (⟨F, hf⟩ : (proEtaleFlatRepresentatives Y R).FullSubcategory)))
      simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
        ObjectProperty.ι_obj, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
        ObjectProperty.FullSubcategory.id_hom, Functor.uncurry_obj_map] at h
      erw [DerivedCategory.Q.{u + 2}.map_id F,
        (((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)).obj (P)).map_id F,
        Category.comp_id] at h
      simpa only [T, Functor.flip_obj_map] using h
    have heq : a.tensor.map (Prod.mkHom (DerivedCategory.Q.{u + 2}.map (q.app P))
        (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) ≫
          a.tensor.map (Prod.mkHom (DerivedCategory.Q.{u + 2}.map p)
            (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) =
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.{u + 2}.map
          (Λ.resolutionFunctor.map p)) (𝟙 (DerivedCategory.Q.{u + 2}.obj F))) ≫ e.hom := by
      change _ = _ ≫ a.tensor.map _
      rw [← a.tensor.map_comp, ← a.tensor.map_comp]
      congr 1
      apply Prod.ext
      · change DerivedCategory.Q.map (q.app P) ≫ DerivedCategory.Q.map p =
          DerivedCategory.Q.map (Λ.resolutionFunctor.map p) ≫
            DerivedCategory.Q.map (q.app A)
        simpa only [← Functor.map_comp, Functor.id_map] using
          congrArg (fun v ↦ DerivedCategory.Q.{u + 2}.map v) (q.naturality p).symm
      · simp
    rw [← Category.assoc, heq, Category.assoc]
    have hez : e.hom ≫ z.hom =
        a.representative.inv.app (⟨PA, hres A⟩, ⟨F, hf⟩) ≫
          DerivedCategory.Q.{u + 2}.map (T.map (q.app A)) := by
      change e.hom ≫ (e.inv ≫ _) = _
      rw [e.hom_inv_id_assoc]
      rfl
    rw [hez, ← Category.assoc, hn]
    rw [← Category.assoc, hn', Category.assoc]
    have hcomm : DerivedCategory.Q.{u + 2}.map (T.map (Λ.resolutionFunctor.map p)) ≫
          DerivedCategory.Q.{u + 2}.map (T.map (q.app A)) =
        DerivedCategory.Q.{u + 2}.map (T.map (q.app P)) ≫
          DerivedCategory.Q.{u + 2}.map (T.map p) := by
      simp only [← Functor.map_comp]
      simpa only [Functor.id_map] using
        congrArg (fun v ↦ DerivedCategory.Q.{u + 2}.map (T.map v)) (q.naturality p)
    simpa only [Category.assoc, T, Functor.flip_obj_map,
      Functor.map₂HomologicalComplex_map_app] using
      congrArg (fun v ↦ a.representative.inv.app (⟨_, hres P⟩, ⟨F, hf⟩) ≫ v) hcomm
  · intro z' hz'
    apply Iso.ext
    apply (cancel_epi (a.tensor.map (Prod.mkHom (DerivedCategory.Q.{u + 2}.map (q.app A))
      (𝟙 (DerivedCategory.Q.{u + 2}.obj F))))).1
    rw [hz' PA (hres A) (q.app A) hqA]
    change _ = e.hom ≫ (e.inv ≫ _)
    rw [e.hom_inv_id_assoc]
    rfl

/-- The unique mixed tensor comparison with the specified resolution normalization.
Source: definition 1264. -/
def proEtaleMixedTensor (a : ProEtaleTensorModel Y R)
    (A F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hf : proEtaleFlatRepresentatives Y R F) :=
  Classical.choose (proEtaleMixedTensor_existsUnique R a A F hf).exists

end AlgebraicGeometry.Scheme
