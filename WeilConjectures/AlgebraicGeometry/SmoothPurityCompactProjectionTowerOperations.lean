/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompactProjectionData
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerLevels
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.SixFunctors.OpenTensorNormalization
import all WeilConjectures.SixFunctors.OpenOperationModels
import all WeilConjectures.SixFunctors.OpenPullbackSupport
import WeilConjectures.SixFunctors.OpenTensorSupport
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.RingedProjectionTensorComparison
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorComparisonOfUniverses
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Operations on a normalized varying coefficient system

Source: Stacks 03D7, 07A4, 03DI, 0GL1 and the finite/tower construction in
blueprint `lem-sp-compact-projection-base-change`, proof step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
open SheafOfModules.OpenTensorNormalization.GeneralizedRinged
open SheafOfModules
open SheafOfModules.GeometricConstruction
open SheafOfModules.CanonicalTensorPullbackOfUniverses
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

set_option synthInstance.maxSize 4096

private theorem ringNatTrans_heq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    {R R' : Cᵒᵖ ⥤ RingCat.{u + 1}} {S S' : Dᵒᵖ ⥤ RingCat.{u + 1}}
    (hR : R = R') (hS : S = S') (a : R ⟶ F.op ⋙ S) (b : R' ⟶ F.op ⋙ S')
    (h : ∀ W, HEq (a.app W).hom (b.app W).hom) : HEq a b := by
  cases hR
  cases hS
  apply heq_of_eq
  apply NatTrans.ext
  funext W
  apply RingCat.hom_ext
  exact eq_of_heq (h W)

private theorem tower_scalar_heq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (c.moduleMap f).hom (spTowerRingMap l E f) := by
  apply ringNatTrans_heq (baseChange .systems f) (hc.1 Y) (hc.1 X)
  intro W
  exact hc.2.1 f W.unop.1 (op W.unop.2)

private theorem pushforward_obj_heq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    {R R' : Cᵒᵖ ⥤ RingCat.{u + 1}} {S S' : Dᵒᵖ ⥤ RingCat.{u + 1}}
    (hR : R = R') (hS : S = S') (a : R ⟶ F.op ⋙ S) (b : R' ⟶ F.op ⋙ S')
    (ha : HEq a b) (M : PresheafOfModules.{u + 1} S)
    (N : PresheafOfModules.{u + 1} S') (hM : HEq M N) :
    HEq ((PresheafOfModules.pushforward a).obj M)
      ((PresheafOfModules.pushforward b).obj N) := by
  cases hR
  cases hS
  cases ha
  cases hM
  rfl

private theorem sheafObj_ext {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    (M N : SheafOfModules.{u + 1} R) (h : M.val = N.val) : M = N := by
  cases M
  cases N
  cases h
  rfl

private theorem tower_push_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eX : spCoefficientTowers l E X ≌ Mod (c.ring X))
    (eY : spCoefficientTowers l E Y ≌ Mod (c.ring Y))
    (hX : ∀ M, HEq (eX.functor.obj M).val M.obj)
    (hY : ∀ M, HEq (eY.functor.obj M).val M.obj)
    (M : spCoefficientTowers l E X) :
    (direct .systems f (c.ring Y) (c.ring X) (c.map f)).obj (eX.functor.obj M) =
      eY.functor.obj ((spTowerPush l E f).obj M) := by
  have hv := (pushforward_obj_heq (baseChange .systems f) (hc.1 Y) (hc.1 X)
    (c.moduleMap f).hom (spTowerRingMap l E f) (tower_scalar_heq l E c hc f)
    (eX.functor.obj M).val M.obj (hX M)).trans
      (hY ((spTowerPush l E f).obj M)).symm
  exact sheafObj_ext _ _ (eq_of_heq hv)


private theorem pushforward_map_heq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    {R R' : Cᵒᵖ ⥤ RingCat.{u + 1}} {S S' : Dᵒᵖ ⥤ RingCat.{u + 1}}
    (hR : R = R') (hS : S = S') (a : R ⟶ F.op ⋙ S) (b : R' ⟶ F.op ⋙ S')
    (ha : HEq a b) {M N : PresheafOfModules.{u + 1} S}
    {M' N' : PresheafOfModules.{u + 1} S'} (hM : HEq M M') (hN : HEq N N')
    (f : M ⟶ N) (g : M' ⟶ N') (hf : HEq f g) :
    HEq ((PresheafOfModules.pushforward a).map f)
      ((PresheafOfModules.pushforward b).map g) := by
  cases hR
  cases hS
  cases ha
  cases hM
  cases hN
  cases hf
  rfl

private theorem sheafHom_heq {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N M' N' : SheafOfModules.{u + 1} R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (hf : HEq f.val g.val) : HEq f g := by
  cases hM
  cases hN
  exact heq_of_eq (SheafOfModules.hom_ext (eq_of_heq hf))

private theorem tower_push_functor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eX : spCoefficientTowers l E X ≌ Mod (c.ring X))
    (eY : spCoefficientTowers l E Y ≌ Mod (c.ring Y))
    (hX : ∀ M, HEq (eX.functor.obj M).val M.obj)
    (hY : ∀ M, HEq (eY.functor.obj M).val M.obj)
    (hmX : ∀ M N (r : M ⟶ N), HEq (eX.functor.map r).val r.hom)
    (hmY : ∀ M N (r : M ⟶ N), HEq (eY.functor.map r).val r.hom) :
    eX.functor ⋙ direct .systems f (c.ring Y) (c.ring X) (c.map f) =
      spTowerPush l E f ⋙ eY.functor := by
  apply Functor.hext (tower_push_obj l E c hc f eX eY hX hY)
  intro M N r
  apply sheafHom_heq
    (tower_push_obj l E c hc f eX eY hX hY M)
    (tower_push_obj l E c hc f eX eY hX hY N)
  exact (pushforward_map_heq (baseChange .systems f) (hc.1 Y) (hc.1 X)
    (c.moduleMap f).hom (spTowerRingMap l E f) (tower_scalar_heq l E c hc f)
    (hX M) (hX N) (eX.functor.map r).val r.hom (hmX M N r)).trans
      (hmY _ _ ((spTowerPush l E f).map r)).symm

private noncomputable def tower_operation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Operation (baseChange .systems f) (c.ring Y) (c.ring X) := by
  let eX := (hc.2.2 X).choose
  let eY := (hc.2.2 Y).choose
  have hX := (hc.2.2 X).choose_spec.2.1
  have hmX := (hc.2.2 X).choose_spec.2.2
  have hY := (hc.2.2 Y).choose_spec.2.1
  have hmY := (hc.2.2 Y).choose_spec.2.2
  let V := direct .systems f (c.ring Y) (c.ring X) (c.map f)
  let L := eY.inverse ⋙ spTowerPullback l E f ⋙ eX.functor
  let s : eX.functor ⋙ V ≅ spTowerPush l E f ⋙ eY.functor :=
    eqToIso (tower_push_functor l E c hc f eX eY hX hY hmX hmY)
  let r : eX.inverse ⋙ spTowerPush l E f ⋙ eY.functor ≅ V :=
    Functor.isoWhiskerLeft eX.inverse s.symm ≪≫
      Functor.isoWhiskerRight eX.counitIso V ≪≫ Functor.leftUnitor V
  let a : L ⊣ V :=
    ((eY.symm.toAdjunction.comp
      (Adjunction.ofIsRightAdjoint (spTowerPush l E f))).comp eX.toAdjunction).ofNatIsoRight r
  have : (SheafOfModules.pushforward.{u + 1} (c.moduleMap f)).IsRightAdjoint :=
    a.isRightAdjoint
  have : (SheafOfModules.pushforward.{u + 1} (c.moduleMap f)).Additive :=
    ⟨by intro M N r s; ext W x; rfl⟩
  have : (SheafOfModules.pullback.{u + 1} (c.moduleMap f)).Additive :=
    (SheafOfModules.pullbackPushforwardAdjunction (c.moduleMap f)).left_adjoint_additive
  have : PreservesFiniteLimits (spTowerPullback l E f) :=
    (sp_tower_operations_properties l E f).1
  have : PreservesFiniteColimits (spTowerPullback l E f) :=
    (sp_tower_operations_properties l E f).2.1
  let e : SheafOfModules.pullback.{u + 1} (c.moduleMap f) ≅ L :=
    (SheafOfModules.pullbackPushforwardAdjunction (c.moduleMap f)).leftAdjointUniq a
  have : PreservesFiniteLimits (SheafOfModules.pullback.{u + 1} (c.moduleMap f)) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (SheafOfModules.pullback.{u + 1} (c.moduleMap f)) :=
    preservesFiniteColimits_of_natIso e.symm
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
    (topology .systems X)
    ((sheafCompose (topology .systems X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring X))
  exact { coefficient := c.moduleMap f }

private theorem constant_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app W ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app W =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
          ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun t ↦ t.app W) h

private theorem constant_square {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (b : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (e : proEtaleBaseChange g ⋙ proEtaleBaseChange b ≅
      proEtaleBaseChange f ⋙ proEtaleBaseChange a) (A : CommRingCat.{u + 1}) :
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A).hom ≫
      Functor.whiskerLeft (proEtaleBaseChange g).op
        (proEtaleConstantDirectImageMap b CommRingCat.{u + 1} A).hom ≫
      Functor.whiskerRight (NatTrans.op e.inv)
        ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj A).obj =
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom ≫
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (proEtaleConstantDirectImageMap a CommRingCat.{u + 1} A).hom := by
  have := Functor.isContinuous_comp (proEtaleBaseChange f) (proEtaleBaseChange a)
    (ProEt.topology Y) (ProEt.topology X) (ProEt.topology X')
  let h : ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A) ⟶
      ((proEtaleBaseChange f ⋙ proEtaleBaseChange a).sheafPushforwardContinuous
        CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X')).obj
          ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj A) := ⟨
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A).hom ≫
      Functor.whiskerLeft (proEtaleBaseChange g).op
        (proEtaleConstantDirectImageMap b CommRingCat.{u + 1} A).hom ≫
      Functor.whiskerRight (NatTrans.op e.inv)
        ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj A).obj⟩
  let k : ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A) ⟶
      ((proEtaleBaseChange f ⋙ proEtaleBaseChange a).sheafPushforwardContinuous
        CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X')).obj
          ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj A) := ⟨
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom ≫
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (proEtaleConstantDirectImageMap a CommRingCat.{u + 1} A).hom⟩
  suffices h = k from congrArg (fun t ↦ t.hom) this
  apply (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change (toSheafify (ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj A)).app W ≫
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A).hom.app W ≫
      (proEtaleConstantDirectImageMap b CommRingCat.{u + 1} A).hom.app
        ((proEtaleBaseChange g).op.obj W) ≫
      ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj A).obj.map
        (e.inv.app W.unop).op =
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app W ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app W ≫
      (proEtaleConstantDirectImageMap a CommRingCat.{u + 1} A).hom.app
        ((proEtaleBaseChange f).op.obj W)
  rw [← Category.assoc, ← Category.assoc, constant_unit]
  rw [constant_unit]
  rw [← Category.assoc, constant_unit, constant_unit]
  have hn := (toSheafify (ProEt.topology X')
    ((Functor.const X'.ProEtᵒᵖ).obj A)).naturality (e.inv.app W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  exact hn.symm.trans (Category.id_comp _)

private theorem ringSquare_transfer
    {C A B D : Type (u + 1)} [Category.{u} C] [Category.{u} A]
    [Category.{u} B] [Category.{u} D]
    (F : C ⥤ A) (G : C ⥤ B) (H : A ⥤ D) (I : B ⥤ D) (e : G ⋙ I ≅ F ⋙ H)
    {R₀ R₀' : Cᵒᵖ ⥤ RingCat.{u + 1}}
    {R₁ R₁' : Aᵒᵖ ⥤ RingCat.{u + 1}}
    {R₂ R₂' : Bᵒᵖ ⥤ RingCat.{u + 1}}
    {R₃ R₃' : Dᵒᵖ ⥤ RingCat.{u + 1}}
    (h₀ : R₀ = R₀') (h₁ : R₁ = R₁') (h₂ : R₂ = R₂') (h₃ : R₃ = R₃')
    (f : R₀ ⟶ F.op ⋙ R₁) (g : R₀ ⟶ G.op ⋙ R₂)
    (h : R₁ ⟶ H.op ⋙ R₃) (i : R₂ ⟶ I.op ⋙ R₃)
    (f' : R₀' ⟶ F.op ⋙ R₁') (g' : R₀' ⟶ G.op ⋙ R₂')
    (h' : R₁' ⟶ H.op ⋙ R₃') (i' : R₂' ⟶ I.op ⋙ R₃')
    (hf : HEq f f') (hg : HEq g g') (hh : HEq h h') (hi : HEq i i')
    (w : g' ≫ Functor.whiskerLeft G.op i' ≫
      Functor.whiskerRight (NatTrans.op e.inv) R₃' = f' ≫ Functor.whiskerLeft F.op h') :
    g ≫ Functor.whiskerLeft G.op i ≫ Functor.whiskerRight (NatTrans.op e.inv) R₃ =
      f ≫ Functor.whiskerLeft F.op h := by
  cases h₀
  cases h₁
  cases h₂
  cases h₃
  cases hf
  cases hg
  cases hh
  cases hi
  exact w

private theorem tower_vertical (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) {U V : T.ProEt} (f : U ⟶ V) :
    (spCoefficientPresheaf l E T).map (Prod.mkHom (𝟙 n) f).op =
      (spCoefficientRing l E T n).obj.map f.op := by
  let F := spCoefficientRings l E T ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}
  change (F.map (𝟙 (op n))).app (op V) ≫ (F.obj (op n)).map f.op = _
  rw [F.map_id]
  exact Category.id_comp _

private theorem tower_ring_square (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) :
    spTowerRingMap l E g ≫ Functor.whiskerLeft (baseChange .systems g).op
        (spTowerRingMap l E b) ≫
      Functor.whiskerRight (NatTrans.op (siteSquare .systems s).inv)
        (spCoefficientPresheaf l E X') =
      spTowerRingMap l E f ≫ Functor.whiskerLeft (baseChange .systems f).op
        (spTowerRingMap l E a) := by
  apply NatTrans.ext
  funext W
  let A := CommRingCat.of (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (W.unop.1 + 1)))
  have h := congrArg (fun k ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    (k.app (op W.unop.2))) (constant_square a b f g (siteSquare .ordinary s) A)
  change spTowerRingMapApp l E g W ≫
    spTowerRingMapApp l E b ((baseChange .systems g).op.obj W) ≫
      (spCoefficientPresheaf l E X').map
        (Prod.mkHom (𝟙 W.unop.1) ((siteSquare .ordinary s).inv.app W.unop.2)).op = _
  rw [tower_vertical]
  exact h

private theorem coefficient_square (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) :
    (c.moduleMap g).hom ≫ Functor.whiskerLeft (baseChange .systems g).op
        (c.moduleMap b).hom ≫
      Functor.whiskerRight (NatTrans.op (siteSquare .systems s).inv)
        ((sheafCompose (topology .systems X')
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring X')).obj =
      (c.moduleMap f).hom ≫ Functor.whiskerLeft (baseChange .systems f).op
        (c.moduleMap a).hom := by
  exact ringSquare_transfer (baseChange .systems f) (baseChange .systems g)
    (baseChange .systems a) (baseChange .systems b) (siteSquare .systems s)
    (hc.1 Y) (hc.1 X) (hc.1 Y') (hc.1 X')
    (c.moduleMap f).hom (c.moduleMap g).hom (c.moduleMap a).hom (c.moduleMap b).hom
    (spTowerRingMap l E f) (spTowerRingMap l E g)
    (spTowerRingMap l E a) (spTowerRingMap l E b)
    (tower_scalar_heq l E c hc f) (tower_scalar_heq l E c hc g)
    (tower_scalar_heq l E c hc a) (tower_scalar_heq l E c hc b)
    (tower_ring_square l E s)

private theorem tower_rightSquare_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) :
    ∃ e : direct .systems b _ _ (c.map b) ⋙ direct .systems g _ _ (c.map g) ≅
        direct .systems a _ _ (c.map a) ⋙ direct .systems f _ _ (c.map f),
      ∀ (M : Mod (c.ring X')) (W : (Site .systems Y)ᵒᵖ),
        HEq (fun x ↦ (e.hom.app M).val.app W x)
          (fun x ↦ M.val.map ((siteSquare .systems s).inv.app W.unop).op x) := by
  let := Functor.isContinuous_comp (baseChange .systems g) (baseChange .systems b)
    (topology .systems Y) (topology .systems Y') (topology .systems X')
  let := Functor.isContinuous_comp (baseChange .systems f) (baseChange .systems a)
    (topology .systems Y) (topology .systems X) (topology .systems X')
  let φ : ((sheafCompose (topology .systems Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring Y)) ⟶
      ((baseChange .systems g ⋙ baseChange .systems b).sheafPushforwardContinuous
        RingCat.{u + 1} (topology .systems Y) (topology .systems X')).obj
          ((sheafCompose (topology .systems X')
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring X')) :=
    ⟨(c.moduleMap g).hom ≫ Functor.whiskerLeft (baseChange .systems g).op
      (c.moduleMap b).hom⟩
  let ψ : ((sheafCompose (topology .systems Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring Y)) ⟶
      ((baseChange .systems f ⋙ baseChange .systems a).sheafPushforwardContinuous
        RingCat.{u + 1} (topology .systems Y) (topology .systems X')).obj
          ((sheafCompose (topology .systems X')
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring X')) :=
    ⟨(c.moduleMap f).hom ≫ Functor.whiskerLeft (baseChange .systems f).op
      (c.moduleMap a).hom⟩
  have he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans
      (siteSquare .systems s).inv RingCat.{u + 1} (topology .systems Y)
        (topology .systems X')).app _ = ψ := by
    apply ObjectProperty.hom_ext
    exact coefficient_square l E c hc s
  let e := SheafOfModules.pushforwardCongr₂ φ (siteSquare .systems s).symm he
  refine ⟨SheafOfModules.pushforwardComp (c.moduleMap g) (c.moduleMap b) ≪≫ e ≪≫
    (SheafOfModules.pushforwardComp (c.moduleMap f) (c.moduleMap a)).symm, ?_⟩
  intro M W
  rfl


set_option maxHeartbeats 1200000 in
-- Elaborate the algebraic adjunction and its sectionwise comparison data.
private theorem normalizedAlgebraicAdjunction_exists
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{u + 1}) (B : Sheaf K CommRingCat.{u + 1})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj A)
    (RI : Sheaf J CommRingCat.{u + 1}) (I : AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset B) (rset A)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ)) :
    ∃ am : I.modules ⋙ tensorFunctor c ⊣
      SheafOfModules.pushforward.{u + 1} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ),
      ∀ M, (mset B).map (am.unit.app M) = adj.homEquiv _ _
        (I.moduleUnderlying.inv.app M ≫ (mset RI).map
          ((tensorAdjunction c).unit.app (I.modules.obj M))) := by
  let V : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)) :=
    F.sheafPushforwardContinuous (Type (u + 1)) K J
  let P := SheafOfModules.pushforward.{u + 1} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let eI := I.moduleUnderlying
  obtain ⟨L₀, hobj₀, hmap₀, V₀, ⟨a₀⟩, hAdd₀⟩ :=
    CategoryTheory.CochainPullback.ringedPullbackPresentation_exists
      (R := B) (S := A) L V adj RI I c
  let p : CategoryTheory.CochainPullback.RingedPullback.{u + 1, u + 1, u, u + 1, u}
      (J := K) (K := J) B A := {
    uInv := L, uPush := V, adj := adj, finiteLimits := inferInstance,
    RI := RI, I := I, coefficient := c, L := L₀, hobj := hobj₀, hmap := hmap₀,
    V := V₀, moduleAdj := a₀, additive := hAdd₀ }
  have hp : CategoryTheory.CochainPullback.structureMap p =
      (adj.homEquiv _ _).symm φs := by
    change I.ringUnderlying.hom ≫ _ = _
    rw [hc]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  have hEquiv (M : Mod B) (H : Mod A) :
      ∃ E : (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)).obj H) ≃ (M ⟶ P.obj H),
        ∀ a, (mset B).map (E a) =
          adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    have ha : CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) ≫ (𝟙 _) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (CategoryTheory.CochainPullback.moduleAddMap A H) := by
      simp only [Category.comp_id, prod.map_id_id, Category.id_comp]
      apply (cancel_epi (prodComparison V ((mset A).obj H) ((mset A).obj H))).mp
      simpa only [IsIso.hom_inv_id_assoc] using (pushforward_operations F A B φ H).symm
    have hs : CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
        prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) ((mset A).obj H)) ≫
          V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) :=
      pushforward_action F A B φ H
    have hg : adj.homEquiv _ _ (CategoryTheory.CochainPullback.structureMap p) = φs := by
      rw [hp, Equiv.apply_symm_apply]
    rw [← hg] at hs
    obtain ⟨E, hE⟩ := CategoryTheory.CochainPullback.linearMate_exists p H (P.obj H)
      (Iso.refl _) ha (by
        simp only [Iso.refl_hom, Category.comp_id]
        convert hs using 1 <;> rfl) M
    exact ⟨E, fun a ↦ by simpa only [Iso.refl_hom, Category.comp_id] using hE a⟩
  choose B' hB using hEquiv
  have hBL {M N} (a : M ⟶ N) H b :
      B' M H (I.modules.map a ≫ b) = a ≫ B' N H b := by
    apply (mset B).map_injective
    rw [hB, (mset B).map_comp, hB, (mset RI).map_comp]
    have hn : eI.inv.app M ≫ (mset RI).map (I.modules.map a) =
        L.map ((mset B).map a) ≫ eI.inv.app N := (eI.inv.naturality a).symm
    rw [← Category.assoc, hn, Category.assoc, adj.homEquiv_naturality_left]
  have hBR M {H H'} a (b : H ⟶ H') :
      B' M H' (a ≫ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)).map b) =
        B' M H a ≫ P.map b := by
    apply (mset B).map_injective
    rw [hB, (mset B).map_comp, hB, (mset RI).map_comp]
    change adj.homEquiv _ _ (eI.inv.app M ≫
      ((mset RI).map a ≫ (mset A).map b)) =
        adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) ≫ V.map ((mset A).map b)
    rw [← Category.assoc, adj.homEquiv_naturality_right]
  let T := I.modules ⋙ tensorFunctor c
  let E' : ∀ M H, (T.obj M ⟶ H) ≃ (M ⟶ P.obj H) :=
    fun M H ↦ ((tensorAdjunction c).homEquiv (I.modules.obj M) H).trans (B' M H)
  have hEL {M N} (a : M ⟶ N) H (b : T.obj N ⟶ H) :
      E' M H (T.map a ≫ b) = a ≫ E' N H b := by
    dsimp only [E', Equiv.trans_apply, T, Functor.comp_map]
    change B' M H ((tensorAdjunction c).homEquiv (I.modules.obj M) H
      ((tensorFunctor c).map (I.modules.map a) ≫ b)) = _
    rw [(tensorAdjunction c).homEquiv_naturality_left, hBL]
    rfl
  let am := Adjunction.mkOfHomEquiv {
    homEquiv := E'
    homEquiv_naturality_left_symm := by
      intro M N H a b
      apply (E' M H).injective
      rw [Equiv.apply_symm_apply, hEL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' a b
      dsimp only [E', Equiv.trans_apply]
      change B' M H' ((tensorAdjunction c).homEquiv (I.modules.obj M) H' (a ≫ b)) = _
      rw [(tensorAdjunction c).homEquiv_naturality_right]
      exact hBR M ((tensorAdjunction c).homEquiv (I.modules.obj M) H a) b }
  refine ⟨am, ?_⟩
  intro M
  change (mset B).map
    (B' M (T.obj M) ((tensorAdjunction c).homEquiv (I.modules.obj M) _ (𝟙 _))) = _
  rw [hB]
  exact congrArg (fun r ↦ adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map r))
    ((tensorAdjunction c).homEquiv_id (I.modules.obj M))

set_option maxHeartbeats 1200000 in
-- Elaborate the algebraic adjunction and its sectionwise comparison data.
private theorem algebraic_tensor_unit
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{u + 1}) (B : Sheaf K CommRingCat.{u + 1})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj A)
    (RI : Sheaf J CommRingCat.{u + 1}) (I : SheafOfModules.AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (am : I.modules ⋙ tensorFunctor c ⊣ SheafOfModules.pushforward.{u + 1}
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ))
    (k : SheafOfModules.CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison
      B A RI L I c (I.modules ⋙ tensorFunctor c) (fun _ ↦ rfl))
    (ham : ∀ M, (mset B).map (am.unit.app M) = adj.homEquiv _ _
      (I.moduleUnderlying.inv.app M ≫ k.q M))
    (M N : Mod B) (W : Dᵒᵖ) (x : M.val.obj W) (y : N.val.obj W) :
    (k.mu M N).hom.val.app (F.op.obj W)
      ((am.unit.app (((tensor B).obj M).obj N)).val.app W (pure B M N W x y)) =
        pure A _ _ (F.op.obj W)
          ((am.unit.app M).val.app W x) ((am.unit.app N).val.app W y) := by
  let Z := (mset B).obj M ⨯ (mset B).obj N
  let px : Z ⟶ (mset B).obj M := prod.fst
  let py : Z ⟶ (mset B).obj N := prod.snd
  let pz := tensorPair B M N Z px py
  let ev := sheafToPresheaf K (Type (u + 1)) ⋙
    (CategoryTheory.evaluation Dᵒᵖ (Type (u + 1))).obj W
  obtain ⟨t, hx, hy⟩ := productElements ev ((mset B).obj M) ((mset B).obj N) x y
  let t' := (adj.unit.app Z).hom.app W t
  have hu (H : Mod B) (z : Z ⟶ (mset B).obj H) :
      (L.map z ≫ I.moduleUnderlying.inv.app H ≫ k.q H).hom.app (F.op.obj W) t' =
        (am.unit.app H).val.app W (z.hom.app W t) := by
    have hn := adj.homEquiv_naturality_left z
      (I.moduleUnderlying.inv.app H ≫ k.q H)
    rw [← ham] at hn
    have hv := congrArg (fun r ↦ r.hom.app W t) hn
    rw [Adjunction.homEquiv_unit] at hv
    change (L.map z ≫ I.moduleUnderlying.inv.app H ≫ k.q H).hom.app (F.op.obj W)
      ((adj.unit.app Z).hom.app W t) =
        (am.unit.app H).val.app W (z.hom.app W t) at hv
    exact hv
  have hz : ∀ V s, pz.hom.app V s =
      SheafOfModules.ringedComparisonPure B M N V (px.hom.app V s) (py.hom.app V s) := by
    intros
    rfl
  have h := k.pure M N Z px py pz hz (F.op.obj W) t'
  change (k.mu M N).hom.val.app (F.op.obj W)
    ((L.map pz ≫ I.moduleUnderlying.inv.app _ ≫ k.q _).hom.app (F.op.obj W) t') = _ at h
  rw [hu, hu, hu] at h
  change px.hom.app W t = x at hx
  change py.hom.app W t = y at hy
  have hz' : pz.hom.app W t = pure B M N W x y := by
    change pure B M N W (px.hom.app W t) (py.hom.app W t) = _
    rw [hx, hy]
  rw [hz', hx, hy] at h
  exact h

private theorem adjunction_unit_coefficient_change
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R : Sheaf J RingCat.{u + 1}} {S : Sheaf K RingCat.{u + 1}}
    (α β : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
    (h : α = β) (T : SheafOfModules.{u + 1} R ⥤ SheafOfModules.{u + 1} S)
    (a : T ⊣ SheafOfModules.pushforward β)
    (A : SheafOfModules.{u + 1} R) (W : Cᵒᵖ) (z : A.val.obj W) :
    ((a.ofNatIsoRight (eqToIso
      (congrArg (fun t ↦ SheafOfModules.pushforward.{u + 1} t) h)).symm).unit.app A).val.app
        W z = (a.unit.app A).val.app W z := by
  cases h
  rfl

set_option maxHeartbeats 1200000 in
-- Elaborate the algebraic adjunction and its sectionwise comparison data.
private theorem algebraicTensor_exists
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) J K)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S)
    (RI : Sheaf K CommRingCat.{u + 1}) (I : SheafOfModules.AlgebraicInverseImage L R RI)
    (c : RI ⟶ S)
    (hc : (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset R) (rset S)).symm
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map φ))
    (o : Operation F R S)
    (ho : o.coefficient = (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) :
    ∃ _mu : o.OrdinaryTensor,
      ∀ P, resolving R P → resolving S ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨am, ham⟩ := normalizedAlgebraicAdjunction_exists F L adj S R φ RI I c hc
  let T := I.modules ⋙ tensorFunctor c
  have hobj (M : Mod R) : T.obj M = SheafOfModules.changeOfRings c (I.modules.obj M) := rfl
  have hmap {M N : Mod R} (a : M ⟶ N) : T.map a = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ := canonicalRingedTensorComparison_existsUnique
    R S RI L I c T hobj _ adj hmap
  have hq (M : Mod R) : k.q M =
      (mset RI).map ((tensorAdjunction c).unit.app (I.modules.obj M)) := by
    ext W m
    exact (k.q_one M W m).trans (((Classical.choose_spec
      (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique c)).1
        (I.modules.obj M) W m).symm)
  have ham' (M : Mod R) : (mset R).map (am.unit.app M) =
      adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ k.q M) := by
    rw [hq]
    exact ham M
  have hpush : o.pushforward = SheafOfModules.pushforward.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) :=
    congrArg (fun t ↦ SheafOfModules.pushforward.{u + 1} t) ho
  let a := am.ofNatIsoRight (eqToIso hpush).symm
  let e := o.moduleAdjunction.leftAdjointUniq a
  let mu : o.OrdinaryTensor := {
    iso := fun M N ↦ e.app _ ≪≫ k.mu M N ≪≫
      ((tensor S).mapIso (e.app M).symm).app _ ≪≫
        ((tensor S).obj (o.pullback.obj M)).mapIso (e.app N).symm
    pure_unit := by
      intro M N W x y
      have he (A : Mod R) : o.moduleAdjunction.unit.app A ≫
          o.pushforward.map (e.hom.app A) = a.unit.app A :=
        o.moduleAdjunction.unit_leftAdjointUniq_hom_app a A
      have hev (A : Mod R) (z : A.val.obj W) :
          (e.hom.app A).val.app (F.op.obj W)
            ((o.moduleAdjunction.unit.app A).val.app W z) =
              (a.unit.app A).val.app W z := by
        exact congrArg (fun r ↦ r.val.app W z) (he A)
      have hinv (A : Mod R) (z : A.val.obj W) :
          (e.inv.app A).val.app (F.op.obj W) ((a.unit.app A).val.app W z) =
            (o.moduleAdjunction.unit.app A).val.app W z := by
        rw [← hev A z]
        exact congrArg (fun r ↦ r.val.app (F.op.obj W)
          ((o.moduleAdjunction.unit.app A).val.app W z)) (e.hom_inv_id_app A)
      have hp := algebraic_tensor_unit F L adj S R φ RI I c am k ham' M N W x y
      have hau (A : Mod R) (z : A.val.obj W) :
          (a.unit.app A).val.app W z = (am.unit.app A).val.app W z := by
        exact adjunction_unit_coefficient_change F o.coefficient _ ho T am A W z
      change (((tensor S).map (e.inv.app M)).app _ ≫
        ((tensor S).obj (o.pullback.obj M)).map (e.inv.app N)).val.app (F.op.obj W)
          ((k.mu M N).hom.val.app (F.op.obj W)
            ((e.hom.app _).val.app (F.op.obj W)
              ((o.moduleAdjunction.unit.app _).val.app W (pure R M N W x y)))) = _
      change (k.mu M N).hom.val.app (F.op.obj W)
        ((am.unit.app (((tensor R).obj M).obj N)).val.app W (pure R M N W x y)) =
          pure S _ _ (F.op.obj W)
            ((am.unit.app M).val.app W x) ((am.unit.app N).val.app W y) at hp
      rw [hev, hau]
      have hp' : (k.mu M N).hom.val.app (F.op.obj W)
          ((am.unit.app (M ⊗ N)).val.app W (pure R M N W x y)) =
            pure S _ _ (F.op.obj W)
              ((a.unit.app M).val.app W x) ((a.unit.app N).val.app W y) := by
        rw [hau, hau]
        exact hp
      apply Eq.trans (congrArg (fun z ↦
        ((((tensor S).map (e.inv.app M)).app _ ≫
          ((tensor S).obj (o.pullback.obj M)).map (e.inv.app N)).val.app
            (F.op.obj W)) z) hp')
      have ht := SheafOfModules.CochainScalarConstruction.pure_map S
        (e.inv.app M) (e.inv.app N) (F.op.obj W)
        ((a.unit.app M).val.app W x) ((a.unit.app N).val.app W y)
      change _ = pure S _ _ _ _ _ at ht
      rw [hinv, hinv] at ht
      exact ht }
  refine ⟨mu, ?_⟩
  intro P hp
  have : (SheafOfModules.pushforward.{u + 1} (F := F) (J := J) (K := K)
      (R := base S) (S := base R)
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)).Additive :=
    ⟨by intro M N f g; ext W x; rfl⟩
  have : T.Additive := am.left_adjoint_additive
  have ht := SheafOfModules.isKFlat_ringedToposPullback L _ adj I c T hobj hmap P hp.1 hp.2
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  refine ⟨SheafOfModules.kFlat_iso_independent S ec.symm ht.1, ?_⟩
  intro n
  let en := (HomologicalComplex.eval _ _ n).mapIso ec
  let := SheafOfModules.monoidalCategory S
  have hf := (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S _) (ht.2 n)
  have hf' := (exactFunctor _ _).prop_of_iso ((tensor S).flip.mapIso en.symm) hf
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S _).symm hf'

open CategoryTheory.Functor.sheafPullbackConstruction in
private theorem tower_tensor_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (o : Operation (baseChange .systems f) (c.ring Y) (c.ring X))
    (ho : o.coefficient = c.moduleMap f) :
    ∃ _mu : o.OrdinaryTensor,
      ∀ P, resolving (c.ring Y) P → resolving (c.ring X)
        ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  have : EssentiallySmall.{u + 1} (Site .systems X) :=
    essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} (Site .systems Y) :=
    essentiallySmallSelf.{0, u, u + 1} _
  have : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat (baseChange .systems f) := by
    constructor
    intro W
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence W.1 W.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  let J := topology .systems Y
  let K := topology .systems X
  let F := baseChange .systems f
  let L := sheafPullback F (Type (u + 1)) J K
  let V := F.sheafPushforwardContinuous (Type (u + 1)) J K
  let adj : L ⊣ V := sheafAdjunctionContinuous F (Type (u + 1)) J K
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  obtain ⟨RI, ⟨I⟩⟩ := algebraicImage_exists J K L V adj (c.ring Y)
  obtain ⟨b, hb⟩ := siteStructuralMap_exists F L adj
    (c.ring X) (c.ring Y) (c.map f) RI I
  exact algebraicTensor_exists F L adj (c.ring Y) (c.ring X) (c.map f) RI I b hb o ho


private theorem constant_open_map_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : CommRingCat.{u + 1}) :
    IsIso (Functor.whiskerLeft (openInclusion .ordinary j).op
      (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} A).hom ≫
        Functor.whiskerRight (NatTrans.op (openSiteAdjunction .ordinary j).unit)
          ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj A).obj) := by
  let G := openInclusion .ordinary j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    openInclusion_continuous .ordinary j
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    openInclusion_cocontinuous .ordinary j
  let P := (Functor.const X.ProEtᵒᵖ).obj A
  let B := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A
  let C := (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj A
  let d : C ≅ restrictRing .ordinary j B :=
    (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)).app P
  let γ : restrictRing .ordinary j B ⟶ C := ⟨
    Functor.whiskerLeft G.op
      (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} A).hom ≫
        Functor.whiskerRight (NatTrans.op (openSiteAdjunction .ordinary j).unit) C.obj⟩
  have h : d.hom ≫ γ = 𝟙 C := by
    apply (sheafificationAdjunction (ProEt.topology U) CommRingCat.{u + 1}).homEquiv _ _
      |>.injective
    apply NatTrans.ext
    funext W
    change _ ≫ _ ≫ _ ≫ _ = _ ≫ 𝟙 _
    have hd := congrArg (fun r ↦ r.app W)
      (G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X) P)
    change (toSheafify (ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj A)).app W ≫
      d.hom.hom.app W =
        (toSheafify (ProEt.topology X) P).app (G.op.obj W) at hd
    rw [← Category.assoc, ← Category.assoc, hd]
    change ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      (G.op.obj W) ≫ (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} A).hom.app
        (G.op.obj W)) ≫ C.obj.map ((openSiteAdjunction .ordinary j).unit.app W.unop).op =
      (toSheafify (ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj A)).app W ≫ 𝟙 _
    rw [constant_unit]
    have hn := (toSheafify (ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj A)).naturality
        ((openSiteAdjunction .ordinary j).unit.app W.unop).op
    change 𝟙 _ ≫ _ = _ at hn
    exact hn.symm.trans ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hγ : γ = d.inv := by
    apply (cancel_epi d.hom).1
    rw [h, d.hom_inv_id]
  change IsIso γ.hom
  rw [hγ]
  infer_instance

private theorem tower_open_map_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (Functor.whiskerLeft (openInclusion .systems j).op (spTowerRingMap l E j) ≫
      Functor.whiskerRight (NatTrans.op (openSiteAdjunction .systems j).unit)
        (spCoefficientPresheaf l E U)) := by
  have hi : ∀ W, IsIso ((Functor.whiskerLeft (openInclusion .systems j).op
      (spTowerRingMap l E j) ≫ Functor.whiskerRight
        (NatTrans.op (openSiteAdjunction .systems j).unit)
          (spCoefficientPresheaf l E U)).app W) := by
    intro W
    let A := CommRingCat.of (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (W.unop.1 + 1)))
    let γ := Functor.whiskerLeft (openInclusion .ordinary j).op
      (proEtaleConstantDirectImageMap j CommRingCat.{u + 1} A).hom ≫
        Functor.whiskerRight (NatTrans.op (openSiteAdjunction .ordinary j).unit)
          ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).obj A).obj
    have : IsIso γ := constant_open_map_isIso j A
    have h : (Functor.whiskerLeft (openInclusion .systems j).op (spTowerRingMap l E j) ≫
        Functor.whiskerRight (NatTrans.op (openSiteAdjunction .systems j).unit)
          (spCoefficientPresheaf l E U)).app W =
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (γ.app (op W.unop.2)) := by
      change spTowerRingMapApp l E j ((openInclusion .systems j).op.obj W) ≫
        (spCoefficientPresheaf l E U).map
          (Prod.mkHom (𝟙 W.unop.1)
            ((openSiteAdjunction .ordinary j).unit.app W.unop.2)).op = _
      rw [tower_vertical]
      rfl
    rw [h]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private theorem adjunct_heq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : G ⊣ F)
    {R R' : Cᵒᵖ ⥤ RingCat.{u + 1}} {S S' : Dᵒᵖ ⥤ RingCat.{u + 1}}
    (hR : R = R') (hS : S = S') (φ : R ⟶ F.op ⋙ S) (φ' : R' ⟶ F.op ⋙ S')
    (hφ : HEq φ φ') :
    HEq (Functor.whiskerLeft G.op φ ≫ Functor.whiskerRight (NatTrans.op a.unit) S)
      (Functor.whiskerLeft G.op φ' ≫ Functor.whiskerRight (NatTrans.op a.unit) S') := by
  cases hR
  cases hS
  cases hφ
  rfl

private theorem isIso_of_heq
    {C : Type (u + 1)} [Category.{u} C] {R R' S S' : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (hR : R = R') (hS : S = S') (φ : R ⟶ S) (φ' : R' ⟶ S')
    (hφ : HEq φ φ') [IsIso φ'] : IsIso φ := by
  cases hR
  cases hS
  cases hφ
  infer_instance

private noncomputable def openRingAdjunct
    (c : Coefficients.{u} .systems) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    ((openInclusion .systems j).sheafPushforwardContinuous RingCat.{u + 1}
      (topology .systems U) (topology .systems X)).obj
        ((sheafCompose (topology .systems X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring X)) ⟶
      ((sheafCompose (topology .systems U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring U)) :=
  (((openSiteAdjunction .systems j).sheafPushforwardContinuous
    (E := RingCat.{u + 1}) (topology .systems U) (topology .systems X)).homEquiv _ _).symm
      (c.moduleMap j)

private theorem open_ring_adjunct_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openRingAdjunct c j) := by
  let a := openSiteAdjunction .systems j
  let γ := openRingAdjunct c j
  have hγ : HEq γ.hom
      (Functor.whiskerLeft (openInclusion .systems j).op (spTowerRingMap l E j) ≫
        Functor.whiskerRight (NatTrans.op a.unit) (spCoefficientPresheaf l E U)) := by
    exact adjunct_heq a (hc.1 X) (hc.1 U) (c.moduleMap j).hom (spTowerRingMap l E j)
      (tower_scalar_heq l E c hc j)
  have := tower_open_map_isIso l E j
  have : IsIso γ.hom := isIso_of_heq
    (congrArg (fun R ↦ (openInclusion .systems j).op ⋙ R) (hc.1 X))
      (hc.1 U) γ.hom _ hγ
  have : IsIso ((sheafToPresheaf (topology .systems U) RingCat.{u + 1}).map γ) :=
    by
      change IsIso γ.hom
      infer_instance
  exact isIso_of_reflects_iso γ (sheafToPresheaf (topology .systems U) RingCat.{u + 1})

private noncomputable def ringIsoModules
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (d : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R := by
  have : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
    Functor.isContinuous_id J
  have : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    Functor.isContinuous_id J
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (CategoryTheory.Equivalence.refl (C := C)) d.hom d.inv
    (by
      change Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ)) S.obj = d.inv.hom ≫ d.hom.hom
      rw [Functor.whiskerRight_id']
      exact (congrArg (fun f ↦ f.hom) d.inv_hom_id).symm)
    (by
      change d.hom.hom ≫ d.inv.hom ≫ Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ)) R.obj = 𝟙 _
      rw [Functor.whiskerRight_id']
      change d.hom.hom ≫ d.inv.hom ≫ 𝟙 R.obj = 𝟙 _
      rw [Category.comp_id]
      exact congrArg (fun f ↦ f.hom) d.hom_inv_id)

private theorem ringIsoModules_functor
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (d : R ≅ S) :
    (ringIsoModules J d).functor = SheafOfModules.pushforward.{u + 1}
      (F := 𝟭 C) (J := J) (K := J) d.hom := rfl

attribute [local irreducible] ringIsoModules

private theorem ringIso_pushforward_comp
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) (G : D ⥤ C) [F.IsContinuous J K] [G.IsContinuous K J]
    (a : G ⊣ F) (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
    (γ : (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R ≅ S)
    (hγ : γ.hom = ((a.sheafPushforwardContinuous (E := RingCat.{u + 1}) K J).homEquiv
      _ _).symm ψ) :
    Nonempty ((ringIsoModules K γ).functor ⋙ SheafOfModules.pushforward.{u + 1}
      ((a.sheafPushforwardContinuous (E := RingCat.{u + 1}) K J).unit.app R) ≅
        SheafOfModules.pushforward.{u + 1} ψ) := by
  let sh := a.sheafPushforwardContinuous (E := RingCat.{u + 1}) K J
  let R' := (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R
  let φ := sh.unit.app R
  have h : φ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map γ.hom = ψ := by
    have hh := (sh.homEquiv _ _).apply_symm_apply ψ
    rw [← hγ] at hh
    exact hh
  have := Functor.isContinuous_comp F (𝟭 D) J K K
  let c : SheafOfModules.pushforward.{u + 1} (F := 𝟭 D) (J := K) (K := K) γ.hom ⋙
      SheafOfModules.pushforward.{u + 1} (F := F) φ ≅
        SheafOfModules.pushforward.{u + 1} (F := F ⋙ 𝟭 D)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map γ.hom) :=
    SheafOfModules.pushforwardComp (F := F) (G := 𝟭 D) (J := J) (K := K) (K' := K)
      (S := R) (R := R') (R' := S) φ γ.hom
  exact ⟨Functor.isoWhiskerRight (eqToIso (ringIsoModules_functor K γ)) _ ≪≫
    c ≪≫ SheafOfModules.pushforwardCongr h⟩

set_option maxHeartbeats 1200000 in
-- Elaborate the algebraic adjunction and its sectionwise comparison data.
private theorem tower_openModel_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : Operation (baseChange .systems j) (c.ring X) (c.ring U))
    (ho : o.coefficient = c.moduleMap j)
    (ox : OpenExtension .systems j (c.ring X)) :
    ∃ (q : Mod (c.ring U) ≌ Mod (restrictRing .systems j (c.ring X)))
      (_e : o.pullback ≅ restrict .systems j (c.ring X) ⋙ q.inverse)
      (om : OpenModel j o), Nonempty (om.functor ≅ q.functor ⋙ ox.ordinary) := by
  have := open_ring_adjunct_isIso l E c hc j
  let γ := asIso (openRingAdjunct c j)
  let q := ringIsoModules (topology .systems U) γ
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products q.functor
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products q.inverse
  let a := openRestrictionAdjunction .systems j (c.ring X)
  obtain ⟨er₀⟩ := ringIso_pushforward_comp (baseChange .systems j)
    (openInclusion .systems j) (openSiteAdjunction .systems j)
    ((sheafCompose (topology .systems X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring X))
    ((sheafCompose (topology .systems U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (c.ring U))
    (c.moduleMap j) γ rfl
  let er : q.functor ⋙ direct .systems j (c.ring X)
      (restrictRing .systems j (c.ring X))
        (openRightCoefficient .systems j (c.ring X)) ≅ o.pushforward :=
    er₀ ≪≫ SheafOfModules.pushforwardCongr ho.symm
  let aj := (a.comp q.symm.toAdjunction).ofNatIsoRight er
  let e := o.moduleAdjunction.leftAdjointUniq aj
  let omAdj := (q.toAdjunction.comp ox.adjunction).ofNatIsoRight e.symm
  have : ∀ M, IsIso (ox.adjunction.unit.app M) := ordinaryUnit_isIso ox
  have hunit : IsIso ox.adjunction.unit :=
    NatIso.isIso_of_isIso_app (α := ox.adjunction.unit)
  have : ox.ordinary.Full := ox.adjunction.fullyFaithfulLOfIsIsoUnit.full
  have : ox.ordinary.Faithful := ox.adjunction.fullyFaithfulLOfIsIsoUnit.faithful
  let om : OpenModel j o := {
    functor := q.functor ⋙ ox.ordinary
    adjunction := omAdj
    additive := omAdj.left_adjoint_additive
    limits := by
      have := ox.limits
      exact comp_preservesFiniteLimits q.functor ox.ordinary
    colimits := by
      have := ox.colimits
      exact comp_preservesFiniteColimits q.functor ox.ordinary
    unit := fun M ↦ by
      have := omAdj.unit_isIso_of_L_fully_faithful
      infer_instance }
  exact ⟨q, e, om, ⟨Iso.refl _⟩⟩

private theorem openModel_essentialImage
    (c : Coefficients.{u} .systems) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (o : Operation (baseChange .systems j) (c.ring X) (c.ring U))
    (q : Mod (c.ring U) ≌ Mod (restrictRing .systems j (c.ring X)))
    [q.functor.Additive] [q.inverse.Additive]
    (e : o.pullback ≅ restrict .systems j (c.ring X) ⋙ q.inverse)
    (om : OpenModel j o) (ox : OpenExtension .systems j (c.ring X))
    (Z : Der (c.ring X)) :
    om.functor.mapDerivedCategory.essImage Z ↔ ox.ordinary.mapDerivedCategory.essImage Z := by
  let a := om.adjunction.ofNatIsoRight e
  let b := q.toAdjunction.comp ox.adjunction
  let k := a.leftAdjointUniq b
  let kd : om.functor.mapDerivedCategory ≅
      q.functor.mapDerivedCategory ⋙ ox.ordinary.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso k ≪≫ Functor.mapDerivedCategoryCompIso _ _
  constructor
  · intro h
    exact Functor.essImage_comp_apply_of_essSurj.mp (Functor.essImage.ofNatIso kd h)
  · intro h
    exact Functor.essImage.ofNatIso kd.symm
      (Functor.essImage_comp_apply_of_essSurj.mpr h)

private theorem openModel_derivedUnit_isIso
    (c : Coefficients.{u} .systems) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (o : Operation (baseChange .systems j) (c.ring X) (c.ring U))
    (om : OpenModel j o) (M : Der (c.ring U)) :
    IsIso ((exactDerivedAdjunction om.adjunction).unit.app M) := by
  let a := exactDerivedAdjunction om.adjunction
  have hQ (P : CochainComplex (Mod (c.ring U)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((om.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have : ∀ n : ℤ,
          IsIso (((om.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ om.unit (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((om.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          o.pullback.mapDerivedCategoryFactors.inv.app _ ≫
            o.pullback.mapDerivedCategory.map
              (om.functor.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, exactDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private theorem openComparisons_of_supported
    (c : Coefficients.{u} .systems) (o : Presentation c)
    (hgamma : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
      (M : Der (c.ring U)) (N : Der (c.ring T)),
      (o.shriek j).essImage ((o.tensor T).functor.obj ((o.shriek j).obj M, N)))
    (hbeta : ∀ {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
      {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
      (_s : IsPullback a j' j h) (M : Der (c.ring X)),
      (o.shriek j').essImage ((o.operation h).left.obj ((o.shriek j).obj M))) :
    OpenComparisons o := by
  have hu {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
      IsIso (o.openAdjunction j).unit := by
    have : ∀ M, IsIso ((o.openAdjunction j).unit.app M) :=
      openModel_derivedUnit_isIso c j (o.operation j) (o.openModel j)
    exact NatIso.isIso_of_isIso_app _
  constructor
  · intro U T j _ M N
    have := hu j
    obtain ⟨Z, ⟨ez⟩⟩ := hgamma j M N
    exact (o.openAdjunction j).isIso_projectionMap_app_app_of_iso
      (o.operation j).left (Functor.curry.obj (o.tensor U).functor)
      (Functor.curry.obj (o.tensor T).functor) (o.curriedTensorComparison j).inv M N Z ez.symm
  · intro X' X B' B a j' j h _ _ s M
    have := hu j
    have := hu j'
    apply isIso_of_adjunct (o.openAdjunction j') (o.betaInv s M) _ (hbeta s M)
    have he : (o.openAdjunction j').homEquiv _ _ (o.betaInv s M) =
        (o.operation a).left.map ((o.openAdjunction j).unit.app M) ≫
          (o.square s.toCommSq).inv.app ((o.shriek j).obj M) := by
      rw [Adjunction.homEquiv_unit]
      exact (unit_mateEquiv_symm (o.openAdjunction j) (o.openAdjunction j')
        (TwoSquare.mk _ _ _ _ (o.square s.toCommSq).inv) M).symm
    rw [he]
    infer_instance

private theorem tower_openModel_image (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : Operation (baseChange .systems j) (c.ring X) (c.ring U))
    (ho : o.coefficient = c.moduleMap j) (om : OpenModel j o)
    (ox : OpenExtension .systems j (c.ring X)) (Z : Der (c.ring X)) :
    om.functor.mapDerivedCategory.essImage Z ↔ ox.ordinary.mapDerivedCategory.essImage Z := by
  obtain ⟨q, e, _, _⟩ := tower_openModel_exists l E c hc j o ho ox
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products q.functor
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products q.inverse
  exact openModel_essentialImage c j o q e om ox Z

private theorem operations_with_tensor_exists (d : Input.{u} .systems)
    (tx : TensorModel d.R) :
    ∃ (t : SiteSquare d) (o : Operations d t), o.tensorX = tx := by
  let t := normalizedSiteSquare d
  obtain ⟨tu⟩ := tensorModel_exists (restrictRing .systems d.j d.R)
  obtain ⟨tx'⟩ := tensorModel_exists d.S
  obtain ⟨tu'⟩ := tensorModel_exists (restrictRing .systems d.j' d.S)
  obtain ⟨o, hx, _, _, _, _⟩ := normalizedOperations_exists d t tx tu tx' tu'
    (normalizedRightSquare t) (normalizedRightSquare_sections t)
  exact ⟨t, o, hx⟩

private theorem exact_pullback_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology .systems Y) CommRingCat.{u + 1})
    (S : Sheaf (topology .systems X) CommRingCat.{u + 1})
    (φ : R ⟶ ((baseChange .systems f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology .systems Y) (topology .systems X)).obj S)
    (o : Operation (baseChange .systems f) R S)
    (ho : o.coefficient = (sheafCompose (topology .systems Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
    (p : Pullback R S (direct .systems f R S φ)) :
    Nonempty (o.left ≅ p.derived) := by
  have : (direct .systems f R S φ).Additive := p.adjunction.right_adjoint_additive
  have := o.kInjectives
  have hp : o.pushforward = direct .systems f R S φ :=
    congrArg (fun t ↦ SheafOfModules.pushforward.{u + 1} t) ho
  let er := Functor.rightDerivedFunctorNatIso (eqToIso hp)
  let a := o.derivedAdjunction.ofNatIsoRight er
  exact ⟨a.leftAdjointUniq (pullback_derivedAdjunction p)⟩

private noncomputable def tower_openInput
    (c : Coefficients.{u} .systems)
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) : Input.{u} .systems where
  U := X
  U' := X'
  X := B
  X' := B'
  gU := a
  j' := j'
  j := j
  g := h
  square := {
    toCommSq := s.toCommSq
    isoPullback := s.isoPullback
    hom_fst := s.isoPullback_hom_fst
    hom_snd := s.isoPullback_hom_snd
    isOpenImmersion := inferInstance
    isOpenImmersion' := inferInstance }
  R := c.ring B
  S := c.ring B'
  coefficient := c.map h

private theorem tower_tensor_supported (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c) (o : Presentation c)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (M : Der (c.ring U)) (N : Der (c.ring T)) :
    (o.shriek j).essImage ((o.tensor T).functor.obj ((o.shriek j).obj M, N)) := by
  let d := tower_openInput c (IsPullback.id_horiz j)
  obtain ⟨t, on, hx⟩ := operations_with_tensor_exists d (o.tensor T)
  obtain ⟨A, ⟨ea⟩⟩ := (tower_openModel_image l E c hc j (o.operation j)
    (o.coefficient j) (o.openModel j) on.opens.extension ((o.shriek j).obj M)).mp
      ((o.shriek j).obj_mem_essImage M)
  have hs := derivedTensor_openSupported on A N
  have hs' : on.opens.jShriek.essImage
      ((o.tensor T).functor.obj ((o.shriek j).obj M, N)) := by
    rw [hx] at hs
    exact Functor.essImage.ofIso ((o.tensor T).functor.mapIso (ea.prod (Iso.refl N))) hs
  exact (tower_openModel_image l E c hc j (o.operation j) (o.coefficient j)
    (o.openModel j) on.opens.extension _).mpr hs'

private theorem tower_pullback_supported (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c) (o : Presentation c)
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (M : Der (c.ring X)) :
    (o.shriek j').essImage ((o.operation h).left.obj ((o.shriek j).obj M)) := by
  let d := tower_openInput c s
  obtain ⟨t, on, _⟩ := operations_with_tensor_exists d (o.tensor B)
  obtain ⟨A, ⟨ea⟩⟩ := (tower_openModel_image l E c hc j (o.operation j)
    (o.coefficient j) (o.openModel j) on.opens.extension ((o.shriek j).obj M)).mp
      ((o.shriek j).obj_mem_essImage M)
  obtain ⟨e⟩ := exact_pullback_comparison h (c.ring B) (c.ring B') (c.map h)
    (o.operation h) (o.coefficient h) on.gPull
  have hs := derivedPullback_openSupported on A
  have hs' : on.opens.jShriek'.essImage
      ((o.operation h).left.obj ((o.shriek j).obj M)) :=
    Functor.essImage.ofIso (on.gPull.derived.mapIso ea ≪≫
      (e.app ((o.shriek j).obj M)).symm) hs
  exact (tower_openModel_image l E c hc j' (o.operation j') (o.coefficient j')
    (o.openModel j') on.opens.extension' _).mpr hs'

private theorem tower_openComparisons (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (hc : TowerCoefficients l E c) (o : Presentation c) :
    OpenComparisons o :=
  openComparisons_of_supported c o (tower_tensor_supported l E c hc o)
    (tower_pullback_supported l E c hc o)


/-- Simultaneous module and derived operations on a normalized varying coefficient system.
This concerns the operations after the actual coefficient system and its equivalence with
coefficient towers have been constructed. It does not assert existence of that system.
Source: blueprint coefficient-tower construction; Stacks 03D7, 03DI, 07A4 and 0GL1
(blueprint: lem-sp-compact-projection-tower-operations).

Proof: use inverse image on the vertical diagram site, leaving the coefficient index fixed.
The specified sectionwise coefficient maps identify inverse image of the ring sheaf with
the target ring sheaf. Module inverse image is therefore exact. The module adjunction,
K-injective resolutions and signed total tensor on flat-term K-flat resolutions supply
Operation and TensorModel. Tensor pullback is fixed by the pure-tensor unit formula and
its total-complex representative equation. The direct-image square is induced by the
iterated fibre-product comparison; evaluate it on sections to obtain rightSections.
For an open immersion the adjoint coefficient map from the restricted ring to the open
ring is invertible (checked at each coefficient level); its ring-isomorphism equivalence
transports exact extension by zero on this same vertical site, whose unit is invertible.
The open tensor-support and pullback-support theorems, applied to normalized operations
with the chosen ambient tensor model, put the sources of the inverse open projection mate
and the inverse open base-change mate in the essential image of extension by zero; their
adjuncts are invertible by the projection-map and mate unit identities, so both mates are
isomorphisms. These constructions are simultaneous in the schemes and maps,
with one derived tensor model at each scheme. They preserve all coefficient transitions;
no scalar extension along quotient-ring reductions is used as an exact functor. -/
theorem normalized_tower_operations_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (_hc : TowerCoefficients l E c) :
    ∃ o : Presentation c, Nonempty (OpenComparisons o) := by
  classical
  let op {X Y : Scheme.{u}} (f : X ⟶ Y) := tower_operation l E c _hc f
  let tx (T : Scheme.{u}) := Classical.choice (tensorModel_exists (c.ring T))
  let mu {X Y : Scheme.{u}} (f : X ⟶ Y) : (op f).OrdinaryTensor :=
    (tower_tensor_exists l E c f (op f) rfl).choose
  have hm {X Y : Scheme.{u}} (f : X ⟶ Y) :
      ∀ P, resolving (c.ring Y) P → resolving (c.ring X)
        (((op f).pullback.mapHomologicalComplex (.up ℤ)).obj P) :=
    (tower_tensor_exists l E c f (op f) rfl).choose_spec
  have hopen {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
      Nonempty (OpenModel j (op j)) := by
    obtain ⟨ox⟩ := systemsOpenExtension_exists j (c.ring T)
    obtain ⟨_, _, om, _⟩ := tower_openModel_exists l E c _hc j (op j) rfl ox
    exact ⟨om⟩
  let o : Presentation c := {
    operation := op
    coefficient := fun _ ↦ rfl
    tensor := tx
    ordinaryTensor := mu
    tensorComparison := fun f ↦ Classical.choice
      (tensor_core (op f) (tx _) (tx _) (mu f) (hm f))
    openModel := fun j ↦ Classical.choice (hopen j)
    rightSquare := fun s ↦ (tower_rightSquare_exists l E c _hc s).choose
    rightSections := fun s ↦ (tower_rightSquare_exists l E c _hc s).choose_spec }
  exact ⟨o, ⟨tower_openComparisons l E c _hc o⟩⟩

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
