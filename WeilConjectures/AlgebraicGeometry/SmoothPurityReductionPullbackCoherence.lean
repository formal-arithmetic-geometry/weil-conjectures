/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
import all WeilConjectures.AlgebraicGeometry.GeometricOrdinaryKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.SecSmoothPurity.CochainCompositeHom
import WeilConjectures.AlgebraicGeometry.CoefficientMonoidalSquareUnit
import WeilConjectures.AlgebraicGeometry.SpSequenceInverseImageLeftExact
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.AlgebraicGeometry.TensorComparisonModelPreservesFlat
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.SystemScalarGenerators
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence
import WeilConjectures.CategoryTheory.SystemScalarCoherence
import all WeilConjectures.Algebra.Homology.RingedKFlatNativeModelIdentification
import WeilConjectures.CategoryTheory.ExactDerivedMonoidalConstruction
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement

/-! # Tensor coherence of a normalized geometric reduction square

Source: Stacks 07A4 and 0D6D; blueprint integral direct-image proof (3).
(blueprint: lem-sp-reduction-pullback-model-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u c v r aD hD

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

open CategoryTheory.MonoidalCategory CategoryTheory.CochainPullback

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical ringed comparison satisfies the ordinary associator and both unit laws. -/
private theorem ringedOrdinaryCore
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    {R : Sheaf J CommRingCat.{max c v r}} {S : Sheaf J' CommRingCat.{max c v r}}
    (f : CategoryTheory.CochainPullback.RingedPullback.{max c v r, c, v, c, v} R S)
    (k : CategoryTheory.CochainPullback.Comparison.{max c v r, c, v, c, v} f) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.monoidalCategory S
    ∃ core : f.L.CoreMonoidal, ∀ M N, (core.μIso M N).inv = (k.mu M N).hom := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  letI := SheafOfModules.symmetricCategory R
  letI := SheafOfModules.symmetricCategory S
  have ha := cochainModuleTensorAssociativity f k
  have hb := cochainModuleTensorBraiding f k
  have hr (M : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) :
      (k.mu M (𝟙_ _)).hom ≫ (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫
        (ρ_ (f.L.obj M)).hom = f.L.map (ρ_ M).hom :=
    CategoryTheory.CochainPullback.module_right_unit f k M
  have hl (M : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) :
      f.L.map (λ_ M).hom = (k.mu (𝟙_ _) M).hom ≫
        ((moduleUnit f k).hom ⊗ₘ 𝟙 _) ≫ (λ_ (f.L.obj M)).hom := by
    calc
      _ = f.L.map (β_ (𝟙_ _) M).hom ≫ f.L.map (ρ_ M).hom := by
        rw [← f.L.map_comp, braiding_rightUnitor]
      _ = f.L.map (β_ (𝟙_ _) M).hom ≫ (k.mu M (𝟙_ _)).hom ≫
          (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫ (ρ_ (f.L.obj M)).hom := by rw [hr]
      _ = (k.mu (𝟙_ _) M).hom ≫ (β_ (f.L.obj (𝟙_ _)) (f.L.obj M)).hom ≫
          (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫ (ρ_ (f.L.obj M)).hom := by
        rw [← Category.assoc, ← Category.assoc, hb, Category.assoc, Category.assoc]
      _ = _ := by rw [← BraidedCategory.braiding_naturality_assoc, braiding_rightUnitor]
  letI : f.L.OplaxMonoidal :=
    { η := (moduleUnit f k).hom
      δ M N := (k.mu M N).hom
      δ_natural_left b N := by
        simpa only [f.L.map_id, tensorHom_id] using (k.naturality b (𝟙 N)).symm
      δ_natural_right M b := by
        simpa only [f.L.map_id, id_tensorHom] using (k.naturality (𝟙 M) b).symm
      oplax_associativity M N H := by simpa only [tensorHom_id, id_tensorHom] using ha M N H
      oplax_left_unitality M := by
        apply (cancel_epi (f.L.map (λ_ M).hom)).1
        simp only [← f.L.map_comp_assoc, Iso.hom_inv_id, f.L.map_id, Category.id_comp]
        rw [hl M, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        simp only [tensorHom_id]
      oplax_right_unitality M := by
        apply (cancel_epi (f.L.map (ρ_ M).hom)).1
        simp only [← f.L.map_comp_assoc, Iso.hom_inv_id, f.L.map_id, Category.id_comp]
        rw [← hr M, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        simp only [id_tensorHom] }
  exact ⟨Functor.CoreMonoidal.mk' (moduleUnit f k).symm (fun M N ↦ (k.mu M N).symm)
    (Functor.OplaxMonoidal.δ_natural_left f.L)
    (Functor.OplaxMonoidal.δ_natural_right f.L)
    (Functor.OplaxMonoidal.associativity f.L)
    (Functor.OplaxMonoidal.left_unitality f.L)
    (Functor.OplaxMonoidal.right_unitality f.L), fun _ _ ↦ rfl⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Remove identity scalar extension, preserving the canonical pure-tensor formula. -/
private theorem inverseOrdinaryCore
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv R S) [I.modules.Additive] :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.monoidalCategory S
    ∃ core : I.modules.CoreMonoidal,
      InverseTensorPure.{c, v, r} J J' uInv R S I
        (fun M N ↦ (core.μIso M N).symm) := by
  classical
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  let A : SheafOfModules.SystemScalarModel.{c, v, max c v r} (𝟙 S) :=
    (SheafOfModules.nonempty_systemScalarModel (𝟙 S)).some
  obtain ⟨G, ⟨hG⟩⟩ :=
    SheafOfModules.CochainInversePairing.inverseImageModuleAdjunction_exists R S
      uInv uPush adj I
  let f : CategoryTheory.CochainPullback.RingedPullback.{max c v r, c, v, c, v} R S := {
    uInv := uInv
    uPush := uPush
    adj := adj
    finiteLimits := inferInstance
    RI := S
    I := I
    coefficient := 𝟙 S
    L := I.modules ⋙ A.model.E
    hobj := fun M ↦ A.model.obj_eq (I.modules.obj M)
    hmap := fun b ↦ A.model.map_eq (I.modules.map b)
    V := _
    moduleAdj := hG.comp A.ordinaryAdj }
  obtain ⟨⟨k⟩, _⟩ :=
    SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_existsUnique
      R S S uInv I (𝟙 S) f.L f.hobj uPush adj f.hmap
  obtain ⟨core, hcore⟩ := ringedOrdinaryCore.{c, v, r} f k
  letI := core.toMonoidal
  let e : f.L ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules (SheafOfModules.systemScalarModelUnit rfl A) ≪≫
      I.modules.rightUnitor
  let m := Functor.Monoidal.coreMonoidalTransport e
  refine ⟨m, ?_⟩
  have hq (M : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) :
      k.q M ≫ (underlying.{c, v, r} J' S).map (e.hom.app M) = 𝟙 _ := by
    ext W x
    change (e.hom.app M).val.app W ((k.q M).hom.app W x) = x
    rw [k.q_one]
    have hu := SheafOfModules.systemScalarModelUnit_tmul rfl A (I.modules.obj M) W 1 x
    convert hu using 1 <;> dsimp [e, SheafOfModules.systemModelTmul] <;>
      simp only [one_smul]
    all_goals rfl
  have hqi (M : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) :
      (underlying.{c, v, r} J' S).map (e.inv.app M) = k.q M := by
    apply (cancel_mono ((underlying.{c, v, r} J' S).map (e.hom.app M))).1
    rw [hq, ← Functor.map_comp, Iso.inv_hom_id_app, (underlying.{c, v, r} J' S).map_id]
  intro M N Z x y z hz W t
  have hp := k.pure M N Z x y z hz W t
  change ((m.μIso M N).inv).val.app W _ = _
  have hm : (m.μIso M N).inv =
      e.inv.app (ordinaryTensor.{c, v, r} J R M N) ≫ (k.mu M N).hom ≫
        (e.hom.app M ⊗ₘ e.hom.app N) := by
    simp only [m, Functor.Monoidal.coreMonoidalTransport_μIso_inv,
      Functor.CoreMonoidal.toOplaxMonoidal_δ, hcore]
  rw [hm]
  change ((e.hom.app M ⊗ₘ e.hom.app N).val.app W)
    ((k.mu M N).hom.val.app W
      ((e.inv.app (ordinaryTensor.{c, v, r} J R M N)).val.app W _)) = _
  have hp' : (k.mu M N).hom.val.app W
      ((e.inv.app (ordinaryTensor.{c, v, r} J R M N)).val.app W
        ((I.moduleUnderlying.inv.app (ordinaryTensor.{c, v, r} J R M N)).hom.app W
          ((uInv.map z).hom.app W t))) =
      tensorSection.{c, v, r} J' S (f.L.obj M) (f.L.obj N) W
        ((k.q M).hom.app W
          ((I.moduleUnderlying.inv.app M).hom.app W ((uInv.map x).hom.app W t)))
        ((k.q N).hom.app W
          ((I.moduleUnderlying.inv.app N).hom.app W ((uInv.map y).hom.app W t))) := by
    have hi := congrArg (fun a ↦ a.hom.app W
      ((I.moduleUnderlying.inv.app (ordinaryTensor.{c, v, r} J R M N)).hom.app W
        ((uInv.map z).hom.app W t))) (hqi (ordinaryTensor.{c, v, r} J R M N))
    with_unfolding_all
      exact (congrArg ((k.mu M N).hom.val.app W) hi).trans hp
  rw [hp']
  rw [show (e.hom.app M ⊗ₘ e.hom.app N).val.app W
      (tensorSection.{c, v, r} J' S (f.L.obj M) (f.L.obj N) W _ _) = _ from
    SheafOfModules.CochainScalarConstruction.pure_map S (e.hom.app M) (e.hom.app N) W _ _]
  congr 1
  · exact congrArg (fun a ↦ a.hom.app W
      ((I.moduleUnderlying.inv.app M).hom.app W ((uInv.map x).hom.app W t))) (hq M)
  · exact congrArg (fun a ↦ a.hom.app W
      ((I.moduleUnderlying.inv.app N).hom.app W ((uInv.map y).hom.app W t))) (hq N)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def coreOfConstraints {D : Type aD} [Category.{hD} D]
    (a r : MonoidalCategory D) (I : D)
    (ua : a.tensorUnit ≅ I) (ur : r.tensorUnit ≅ I)
    (e : @tensor D _ a ≅ @tensor D _ r)
    (hc : RingedKFlatModel.Constraints a r I ua ur e) :
    @Functor.CoreMonoidal D _ a D _ r (𝟭 D) := by
  let ta := @tensor D _ a
  let tr := @tensor D _ r
  have hl (X : D) :
      e.hom.app (a.tensorUnit, X) ≫ tr.map (X := (a.tensorUnit, X)) (Y := (r.tensorUnit, X))
        (Prod.mkHom (ua.hom ≫ ur.inv) (𝟙 X)) ≫
        (r.leftUnitor X).hom = (a.leftUnitor X).hom := by
    have hn := e.hom.naturality (Prod.mkHom ua.hom (𝟙 X))
    have hh := congrArg (fun f ↦ ta.map (X := (a.tensorUnit, X)) (Y := (I, X))
      (Prod.mkHom ua.hom (𝟙 X)) ≫ f) (hc.2.1 X)
    dsimp only [ta, tr] at hn hh ⊢
    simp only [← Category.assoc] at hh
    rw [hn] at hh
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Category.comp_id, Prod.mkHom, prod_comp, ← prod_id'] at hh
    simpa only [(@tensor D _ a).map_id, Category.id_comp, Prod.mkHom] using hh
  have hr (X : D) :
      e.hom.app (X, a.tensorUnit) ≫ tr.map (X := (X, a.tensorUnit)) (Y := (X, r.tensorUnit))
        (Prod.mkHom (𝟙 X) (ua.hom ≫ ur.inv)) ≫
        (r.rightUnitor X).hom = (a.rightUnitor X).hom := by
    have hn := e.hom.naturality (Prod.mkHom (𝟙 X) ua.hom)
    have hh := congrArg (fun f ↦ ta.map (X := (X, a.tensorUnit)) (Y := (X, I))
      (Prod.mkHom (𝟙 X) ua.hom) ≫ f) (hc.2.2 X)
    dsimp only [ta, tr] at hn hh ⊢
    simp only [← Category.assoc] at hh
    rw [hn] at hh
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Category.comp_id, Prod.mkHom, prod_comp, ← prod_id'] at hh
    simpa only [(@tensor D _ a).map_id, Category.id_comp, Prod.mkHom] using hh
  refine @Functor.CoreMonoidal.mk' D _ a D _ r (𝟭 D)
    (ur ≪≫ ua.symm)
    (fun X Y ↦ (e.app (X, Y)).symm)
    (μIso_inv_natural_left := fun f X ↦ by
      simpa only [Functor.id_map, Functor.id_obj, Iso.symm_inv, Iso.app_hom, tensor_map,
        @tensorHom_id D _ a, @tensorHom_id D _ r] using
        (e.hom.naturality (Prod.mkHom f (𝟙 X))).symm)
    (μIso_inv_natural_right := fun X f ↦ by
      simpa only [Functor.id_map, Functor.id_obj, Iso.symm_inv, Iso.app_hom, tensor_map,
        @id_tensorHom D _ a, @id_tensorHom D _ r] using
        (e.hom.naturality (Prod.mkHom (𝟙 X) f)).symm)
    (oplax_associativity := fun X Y Z ↦ by
      simpa only [Functor.id_map, Functor.id_obj, Iso.symm_inv, Iso.app_hom, tensor_map,
        @tensorHom_id D _ a, @tensorHom_id D _ r,
        @id_tensorHom D _ a, @id_tensorHom D _ r] using hc.1 X Y Z)
    (oplax_left_unitality := fun X ↦ by
      change (r.leftUnitor X).inv = (a.leftUnitor X).inv ≫ e.hom.app (a.tensorUnit, X) ≫
        r.whiskerRight (ua.hom ≫ ur.inv) X
      apply (cancel_mono (r.leftUnitor X).hom).1
      have hh := hl X
      simp only [tr, tensor_map, @tensorHom_id D _ r] at hh
      rw [Category.assoc, Category.assoc, hh, Iso.inv_hom_id, Iso.inv_hom_id])
    (oplax_right_unitality := fun X ↦ by
      change (r.rightUnitor X).inv = (a.rightUnitor X).inv ≫ e.hom.app (X, a.tensorUnit) ≫
        r.whiskerLeft X (ua.hom ≫ ur.inv)
      apply (cancel_mono (r.rightUnitor X).hom).1
      have hh := hr X
      simp only [tr, tensor_map, @id_tensorHom D _ r] at hh
      rw [Category.assoc, Category.assoc, hh, Iso.inv_hom_id, Iso.inv_hom_id])
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The normalized native-to-prescribed comparison is strong monoidal. -/
private theorem endpointCore
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
    (A : SemilinearSections.Closed.{c, v, r} J R) (TA : Models.{c, v, r} J R A)
    (sym : @SymmetricCategory _ _ A.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, r, (max c v r) + 1} J R A TA sym) :
    ∃ core : @Functor.CoreMonoidal _ _
        (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) _ _
        A.monoidal (𝟭 (DerivedCategory
          (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R))),
      ∀ (P Q : CochainComplex (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
        (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
        (RingedDerivedNative.tensorIso.{c, v, r, (max c v r) + 1} J R P Q (Or.inl hP)).hom ≫
          (@Functor.CoreMonoidal.μIso _ _
            (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) _ _
            A.monoidal (𝟭 _) core (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv =
            (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).hom := by
  obtain ⟨e, he⟩ := RingedKFlatModel.comparison_exists.{c, v, r, (max c v r) + 1} J R A TA
  have hc := RingedKFlatModel.comparison_constraints.{c, v, r, (max c v r) + 1}
    J R A TA sym coh e he
  with_unfolding_all
    refine ⟨coreOfConstraints
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) A.monoidal
    (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R))
    (RingedDerivedNative.unitIso.{c, v, r, (max c v r) + 1} J R) coh.unitIso e hc, ?_⟩
  intro P Q hP hQ
  exact he P Q hP hQ

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem reverseIdentityCore
    {D : Type aD} [Category.{hD} D] (a b : MonoidalCategory D)
    (s : @Functor.CoreMonoidal D _ a D _ b (𝟭 D)) :
    ∃ t : @Functor.CoreMonoidal D _ b D _ a (𝟭 D),
      ∀ X Y, (@Functor.CoreMonoidal.μIso D _ b D _ a (𝟭 D) t X Y) =
        (@Functor.CoreMonoidal.μIso D _ a D _ b (𝟭 D) s X Y).symm := by
  let sm := @Functor.CoreMonoidal.toMonoidal D _ a D _ b (𝟭 D) s
  let em : @Functor.Monoidal D _ b D _ a (𝟭 D) :=
    @CategoryTheory.Equivalence.inverseMonoidal D _ a D _ b
      (CategoryTheory.Equivalence.refl (C := D)) sm
  letI : @Functor.Monoidal D _ b D _ a (𝟭 D) := em
  let t := @Functor.CoreMonoidal.ofLaxMonoidal D _ b D _ a (𝟭 D)
    em.toLaxMonoidal inferInstance (fun _ _ ↦ inferInstance)
  refine ⟨t, ?_⟩
  intro X Y
  apply Iso.ext
  change @Functor.LaxMonoidal.μ D _ b D _ a (𝟭 D) em.toLaxMonoidal X Y =
    (@Functor.CoreMonoidal.μIso D _ a D _ b (𝟭 D) s X Y).inv
  change 𝟙 _ ≫ ((𝟭 D).map ((@Functor.CoreMonoidal.μIso D _ a D _ b (𝟭 D) s X Y).inv) ≫ _) = _
  simp [CategoryTheory.Equivalence.refl_toAdjunction, Adjunction.id]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def composeCore
    {A B C : Type*} [Category A] [Category B] [Category C]
    [ma : MonoidalCategory A] [mb : MonoidalCategory B] [mc : MonoidalCategory C]
    (F : A ⥤ B) (G : B ⥤ C)
    (f : F.CoreMonoidal) (g : G.CoreMonoidal) : (F ⋙ G).CoreMonoidal := by
  letI := f.toMonoidal
  letI := g.toMonoidal
  exact Functor.CoreMonoidal.ofOplaxMonoidal (F ⋙ G)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem inversePreservesFlat
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv R S) :
    letI := SheafOfModules.cochainModulesMonoidal R
    letI := SheafOfModules.cochainModulesMonoidal S
    I.modules.PreservesFlat := by
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesMonoidal S
  constructor
  intro M hM
  have hflat : SheafOfModules.IsFlatOnSite (J := J) (R := R) M :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm hM.2
  have hF : SheafOfModules.IsFlatOnSite (J := J') (R := S) (I.modules.obj M) :=
    SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{c, v, c, v,
      max c v r, max c v r} uInv uPush adj
      (SheafOfModules.inverseImageOfUniverses.{c, v, c, v, max c v r} I) M hflat
  have hright : exactFunctor _ _ (tensorRight (I.modules.obj M)) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso S _) hF
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight (I.modules.obj M)).symm hright, hright⟩

set_option maxHeartbeats 4000000 in
-- Transport through two endpoint monoidal structures before normalizing representatives.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Transport the native exact derived comparison to the prescribed endpoint models. -/
private theorem inverseDerivedCore
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv R S)
    [I.modules.Additive] [PreservesFiniteLimits I.modules]
    [PreservesFiniteColimits I.modules] [PreservesColimitsOfSize.{0, 0} I.modules]
    (m : @Functor.CoreMonoidal _ _ (SheafOfModules.cochainModulesMonoidal R)
      _ _ (SheafOfModules.cochainModulesMonoidal S) I.modules)
    (A : SemilinearSections.Closed.{c, v, r} J R)
    (B : SemilinearSections.Closed.{c, v, r} J' S)
    (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} J' S B)
    (symA : @SymmetricCategory _ _ A.monoidal)
    (cohA : RingedDerivedTensorCoherence.{c, v, r, (max c v r) + 1} J R A TA symA)
    (symB : @SymmetricCategory _ _ B.monoidal)
    (cohB : RingedDerivedTensorCoherence.{c, v, r, (max c v r) + 1} J' S B TB symB) :
    ∃ d : @Functor.CoreMonoidal _ _ A.monoidal _ _ B.monoidal
        I.modules.mapDerivedCategory,
      ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
        (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
        (hFP : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := S)
          ((I.modules.mapHomologicalComplex (.up ℤ)).obj P))
        (hFQ : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := S)
          ((I.modules.mapHomologicalComplex (.up ℤ)).obj Q)),
      I.modules.mapDerivedCategory.map (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).hom ≫
        (@Functor.CoreMonoidal.μIso _ _ A.monoidal _ _ B.monoidal
          I.modules.mapDerivedCategory d (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv ≫
        B.tensor.map (Prod.mkHom (I.modules.mapDerivedCategoryFactors.hom.app P)
          (I.modules.mapDerivedCategoryFactors.hom.app Q)) =
      I.modules.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (letI := m.toMonoidal
          (Functor.mapCochainComplexμIso I.modules P Q).inv) ≫
        (tensorModelIso.{c, v, r} J' S B TB
          ((I.modules.mapHomologicalComplex (.up ℤ)).obj P)
          ((I.modules.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ).hom := by
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesMonoidal S
  letI := SheafOfModules.cochainModulesSymmetric R
  letI := SheafOfModules.cochainModulesSymmetric S
  letI := SheafOfModules.cochainModulesPreadditive R
  letI := SheafOfModules.cochainModulesPreadditive S
  letI : MonoidalClosed (SemilinearSections.Mod.{c, v, max c v r} J R) :=
    (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  letI : MonoidalClosed (SemilinearSections.Mod.{c, v, max c v r} J' S) :=
    (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := S)).some
  letI : IsGrothendieckAbelian.{max c v r}
      (SemilinearSections.Mod.{c, v, max c v r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  letI : IsGrothendieckAbelian.{max c v r}
      (SemilinearSections.Mod.{c, v, max c v r} J' S) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J' S).1
  letI := SheafOfModules.hasFunctorialFlatResolution_kfi R
  letI := SheafOfModules.hasFunctorialFlatResolution_kfi S
  letI := hasColimitsOfSizeShrink.{0, 0, max c v r, max c v r}
    (SemilinearSections.Mod.{c, v, max c v r} J R)
  letI := hasColimitsOfSizeShrink.{0, 0, max c v r, max c v r}
    (SemilinearSections.Mod.{c, v, max c v r} J' S)
  letI := m.toMonoidal
  obtain ⟨G, ⟨hG⟩⟩ :=
    SheafOfModules.CochainInversePairing.inverseImageModuleAdjunction_exists
      R S uInv uPush adj I
  letI := hG.leftAdjoint_preservesColimits
  letI := inversePreservesFlat.{c, v, r} J J' R S uInv uPush adj I
  obtain ⟨native, hnative⟩ :=
    ConstantModuleDerivedProjection.exact_monoidal_normalization I.modules m.toMonoidal
  obtain ⟨source, hsource⟩ := endpointCore.{c, v, r} J R A TA symA cohA
  obtain ⟨target, htarget⟩ := endpointCore.{c, v, r} J' S B TB symB cohB
  obtain ⟨sourceInv, hsourceInv⟩ := reverseIdentityCore _ _ source
  letI : @Functor.Monoidal _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S)
    I.modules.mapDerivedCategory := native
  let nativeCore := @Functor.CoreMonoidal.ofOplaxMonoidal _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S)
    I.modules.mapDerivedCategory native.toOplaxMonoidal inferInstance (fun _ _ ↦ inferInstance)
  let pre := @composeCore _ _ _ _ _ _ A.monoidal
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R)
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S)
    (𝟭 _) I.modules.mapDerivedCategory sourceInv nativeCore
  let d := @composeCore _ _ _ _ _ _ A.monoidal
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S) B.monoidal
    I.modules.mapDerivedCategory (𝟭 _) pre target
  refine ⟨d, ?_⟩
  intro P Q hP hQ hFP hFQ
  let F := I.modules.mapDerivedCategory
  let x := DerivedCategory.Q.obj P
  let y := DerivedCategory.Q.obj Q
  let FP := (I.modules.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (I.modules.mapHomologicalComplex (.up ℤ)).obj Q
  let eP := I.modules.mapDerivedCategoryFactors.app P
  let eQ := I.modules.mapDerivedCategoryFactors.app Q
  let eT := I.modules.mapDerivedCategoryFactors.app ((totalTensor.{c, v, r} J R).obj (P, Q))
  let ns := RingedDerivedNative.tensorIso.{c, v, r, (max c v r) + 1} J R P Q (Or.inl hP)
  let nt := RingedDerivedNative.tensorIso.{c, v, r, (max c v r) + 1} J' S FP FQ (Or.inl hFP)
  let sc X Y := @Functor.CoreMonoidal.μIso _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) _ _
    A.monoidal (𝟭 _) source X Y
  let tc X Y := @Functor.CoreMonoidal.μIso _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S) _ _
    B.monoidal (𝟭 _) target X Y
  let nd X Y := @Functor.OplaxMonoidal.δ _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R) _ _
    (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S)
    F native.toOplaxMonoidal X Y
  let tn := @tensor _ _ (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S)
  have hd : (@Functor.CoreMonoidal.μIso _ _ A.monoidal _ _ B.monoidal F d x y).inv =
      F.map (sc x y).hom ≫ nd x y ≫ (tc (F.obj x) (F.obj y)).inv := by
    change (F.map ((@Functor.CoreMonoidal.μIso _ _ A.monoidal _ _
      (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J R)
      (𝟭 _) sourceInv x y).inv) ≫ nd x y) ≫ (tc (F.obj x) (F.obj y)).inv = _
    rw [hsourceInv]
    simp only [Iso.symm_inv, Category.assoc]
    rfl
  have hs : F.map (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).hom ≫
      F.map (sc x y).hom = F.map ns.hom := by
    rw [← hsource P Q hP hQ, ← F.map_comp]
    congr 1
    simp only [sc, x, y, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  letI := A.monoidal
  letI := B.monoidal
  have ht : (tc (F.obj x) (F.obj y)).inv ≫
      B.tensor.map (Prod.mkHom eP.hom eQ.hom) =
      tn.map (Prod.mkHom eP.hom eQ.hom) ≫
        (tc (DerivedCategory.Q.obj FP) (DerivedCategory.Q.obj FQ)).inv := by
    exact @Functor.OplaxMonoidal.δ_natural _ _
      (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S) _ _
      B.monoidal (𝟭 _)
      (@Functor.CoreMonoidal.toOplaxMonoidal _ _
        (RingedDerivedNative.monoidal.{c, v, r, (max c v r) + 1} J' S)
        _ _ B.monoidal (𝟭 _) target) _ _ _ _ eP.hom eQ.hom
  have hn := hnative P Q ((RingedKFlatModel.kFlat_iff.{c, v, r} J R P).1 hP)
    ((RingedKFlatModel.kFlat_iff.{c, v, r} J R Q).1 hQ)
  change nd x y ≫ tn.map (Prod.mkHom eP.hom eQ.hom) ≫ nt.inv =
    F.map ns.inv ≫ eT.hom ≫ DerivedCategory.Q.map
      (Functor.mapCochainComplexμIso I.modules P Q).inv at hn
  have hn' := congrArg (fun w ↦ F.map ns.hom ≫ w ≫ nt.hom) hn
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp] at hn'
  change F.map (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).hom ≫
    (@Functor.CoreMonoidal.μIso _ _ A.monoidal _ _ B.monoidal F d x y).inv ≫
      B.tensor.map (Prod.mkHom eP.hom eQ.hom) = _
  rw [hd]
  simp only [Category.assoc]
  rw [reassoc_of% hs, ht]
  rw [reassoc_of% hn']
  have htarget' := htarget FP FQ hFP hFQ
  change nt.hom ≫ (tc _ _).inv = _ at htarget'
  rw [htarget']
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The normalized transpose of a module map, with its underlying set-level formula. -/
private theorem inverseLinearMate
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv R S)
    (H : SemilinearSections.Mod.{c, v, max c v r} J' S) :
    ∃ (P : SemilinearSections.Mod.{c, v, max c v r} J R)
      (e : (underlying.{c, v, r} J R).obj P ≅
        uPush.obj ((underlying.{c, v, r} J' S).obj H)),
      ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R),
        ∃ E : (I.modules.obj M ⟶ H) ≃ (M ⟶ P),
          ∀ a, (underlying.{c, v, r} J R).map (E a) ≫ e.hom =
            adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫
              (underlying.{c, v, r} J' S).map a) := by
  let A : SheafOfModules.SystemScalarModel.{c, v, max c v r} (𝟙 S) :=
    (SheafOfModules.nonempty_systemScalarModel (𝟙 S)).some
  let f : CategoryTheory.CochainCompositeHom.RingedPullback.{max c v r, c, v, c, v} R S := {
    uInv := uInv
    uPush := uPush
    adj := adj
    finiteLimits := inferInstance
    RI := S
    I := I
    coefficient := 𝟙 S
    L := I.modules ⋙ A.model.E
    hobj := fun M ↦ A.model.obj_eq (I.modules.obj M)
    hmap := fun a ↦ A.model.map_eq (I.modules.map a) }
  obtain ⟨P, e, ha, hs⟩ := CategoryTheory.CochainCompositeHom.directModule_exists f H
  refine ⟨P, e, ?_⟩
  intro M
  obtain ⟨E, hE⟩ := CategoryTheory.CochainCompositeHom.linearMate_exists f H P e ha hs M
  let er := (SheafOfModules.systemScalarRestrictionUnit (𝟙 S) rfl).app H
  let E' : (I.modules.obj M ⟶ H) ≃ (M ⟶ P) :=
    (Iso.homCongr (Iso.refl _) er.symm).trans E
  refine ⟨E', ?_⟩
  intro a
  change (underlying.{c, v, r} J R).map (E (a ≫ er.inv)) ≫ e.hom = _
  rw [hE]
  congr 1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem invertTensorEquation
    {C : Type aD} [Category.{hD} C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₀ ≅ X₄) (e : X₅ ≅ X₄) (t : X₅ ≅ X₃)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.inv ≫ t.hom) :
    b.inv ≫ a.inv ≫ d.hom = c.hom ≫ t.inv ≫ e.hom := by
  apply (cancel_epi (a.hom ≫ b.hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 800000 in
-- The predicate records two independent endpoint models.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def FullTensorNormalization
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (F : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
      SemilinearSections.Mod.{c, v, max c v r} J' S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (A : SemilinearSections.Closed.{c, v, r} J R)
    (B : SemilinearSections.Closed.{c, v, r} J' S)
    (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} J' S B)
    (mu : A.tensor ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor)
    (model : TensorComparisonModel.{c, v, r} J J' R S F A B TA TB mu) : Prop :=
  ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hFP : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := S)
      ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hFQ : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := S)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)),
    mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      F.mapDerivedCategory.map (tensorModelIso.{c, v, r} J R A TA P Q hP hQ).inv ≫
      F.mapDerivedCategoryFactors.hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) =
    B.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.hom.app P)
      (F.mapDerivedCategoryFactors.hom.app Q)) ≫
      (tensorModelIso.{c, v, r} J' S B TB
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ).inv ≫
      DerivedCategory.Q.map (model.chain P Q)

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Construct the normalized model and its coherent tensorator together. -/
private theorem inverseMonoidalModel
    {C C' : Type c} [Category.{v} C] [Category.{v} C']
    [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv R S)
    [I.modules.Additive] [PreservesFiniteLimits I.modules]
    [PreservesFiniteColimits I.modules]
    (A : SemilinearSections.Closed.{c, v, r} J R) (B : SemilinearSections.Closed.{c, v, r} J' S)
    (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} J' S B)
    (symA : @SymmetricCategory _ _ A.monoidal)
    (cohA : RingedDerivedTensorCoherence.{c, v, r, (max c v r) + 1} J R A TA symA)
    (symB : @SymmetricCategory _ _ B.monoidal)
    (cohB : RingedDerivedTensorCoherence.{c, v, r, (max c v r) + 1} J' S B TB symB) :
    ∃ mu : A.tensor ⋙ I.modules.mapDerivedCategory ≅
        (I.modules.mapDerivedCategory.prod I.modules.mapDerivedCategory) ⋙ B.tensor,
      ∃ model : TensorComparisonModel.{c, v, r} J J' R S I.modules A B TA TB mu,
      ∃ core : @Functor.CoreMonoidal _ _ A.monoidal _ _ B.monoidal
          I.modules.mapDerivedCategory,
        InverseTensorPure.{c, v, r} J J' uInv R S I model.ordinary ∧
        (∀ X Y, (@Functor.CoreMonoidal.μIso _ _ A.monoidal _ _ B.monoidal
          I.modules.mapDerivedCategory core X Y).hom = mu.inv.app (X, Y)) ∧
        FullTensorNormalization.{c, v, r} J J' R S I.modules A B TA TB mu model := by
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesMonoidal S
  obtain ⟨m, hp⟩ := inverseOrdinaryCore.{c, v, r} J J' R S uInv uPush adj I
  letI := m.toMonoidal
  obtain ⟨G, ⟨hG⟩⟩ :=
    SheafOfModules.CochainInversePairing.inverseImageModuleAdjunction_exists
      R S uInv uPush adj I
  letI := hG.leftAdjoint_preservesColimits
  obtain ⟨core, hc⟩ := inverseDerivedCore.{c, v, r} J J' R S uInv uPush adj I m
    A B TA TB symA cohA symB cohB
  letI := A.monoidal
  letI := B.monoidal
  letI := core.toMonoidal
  let mu : A.tensor ⋙ I.modules.mapDerivedCategory ≅
      (I.modules.mapDerivedCategory.prod I.modules.mapDerivedCategory) ⋙ B.tensor :=
    (Functor.Monoidal.μNatIso I.modules.mapDerivedCategory).symm
  let hk := inverse_kflat.{c, v, r} J J' uInv uPush adj R S I
  let model : TensorComparisonModel.{c, v, r} J J' R S I.modules A B TA TB mu := {
    ordinary := fun M N ↦ (m.μIso M N).symm
    chain := fun P Q ↦ (Functor.mapCochainComplexμIso I.modules P Q).hom
    summand := by
      intro P Q p q k h
      with_unfolding_all exact I.modules.ιTensorObj_mapCochainComplexμIso_hom_f P Q p q k h
    kflat := hk
    derived := by
      intro P Q hP hQ fP fQ
      let s := tensorModelIso.{c, v, r} J R A TA P Q hP hQ
      let t := tensorModelIso.{c, v, r} J' S B TB
        ((I.modules.mapHomologicalComplex (.up ℤ)).obj P)
        ((I.modules.mapHomologicalComplex (.up ℤ)).obj Q) (hk P hP fP) (hk Q hQ fQ)
      let e := Functor.mapCochainComplexμIso I.modules P Q
      let b := B.tensor.mapIso ((I.modules.mapDerivedCategoryFactors.app P).prod
        (I.modules.mapDerivedCategoryFactors.app Q))
      have hn := hc P Q hP hQ (hk P hP fP) (hk Q hQ fQ)
      have hi := invertTensorEquation (I.modules.mapDerivedCategory.mapIso s)
        (mu.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) b
        (I.modules.mapDerivedCategoryFactors.app ((totalTensor.{c, v, r} J R).obj (P, Q)))
        (DerivedCategory.Q.mapIso e) t hn
      have he := congrArg (fun f ↦ t.hom ≫ b.inv ≫ f) hi
      simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] at he
      simpa only [s, t, e, b, Functor.mapIso_hom, Functor.mapIso_inv,
        Iso.prod_inv, Iso.app_inv, Iso.app_hom] using he
  }
  refine ⟨mu, model, core, hp, (fun _ _ ↦ rfl), ?_⟩
  intro P Q hP hQ hFP hFQ
  let s := tensorModelIso.{c, v, r} J R A TA P Q hP hQ
  let t := tensorModelIso.{c, v, r} J' S B TB
    ((I.modules.mapHomologicalComplex (.up ℤ)).obj P)
    ((I.modules.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ
  have hn := hc P Q hP hQ hFP hFQ
  exact invertTensorEquation (I.modules.mapDerivedCategory.mapIso s)
    (mu.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (B.tensor.mapIso ((I.modules.mapDerivedCategoryFactors.app P).prod
      (I.modules.mapDerivedCategoryFactors.app Q)))
    (I.modules.mapDerivedCategoryFactors.app ((totalTensor.{c, v, r} J R).obj (P, Q)))
    (DerivedCategory.Q.mapIso (Functor.mapCochainComplexμIso I.modules P Q)) t hn

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem kanSection_map
    {C C' : Type (u + 1)} [Category.{u} C] [Category.{u} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [HasWeakSheafify J' (Type (u + 1))]
    (G : C ⥤ C') [G.IsContinuous J J']
    {M N : Sheaf J (Type (u + 1))} (f : M ⟶ N) (V : Cᵒᵖ) (x : M.obj.obj V) :
    ((Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) J J').map f).hom.app
        (G.op.obj V) (AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G M V x) =
      AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G N V (f.hom.app V x) := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    G (Type (u + 1)) J J'
  have hn := congrArg (fun k ↦ k.hom.app V x) (adj.unit.naturality f)
  exact hn.symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def kanModuleSection
    {C C' : Type (u + 1)} [Category.{u} C] [Category.{u} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [HasWeakSheafify J' (Type (u + 1))]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} C']
    (G : C ⥤ C')
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf J' CommRingCat.{u + 1})
    (I : SheafOfModules.AlgebraicInverseImage
      (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) J J') R S)
    (M : SemilinearSections.Mod.{u + 1, u, u + 1} J R) (V : Cᵒᵖ) (x : M.val.obj V) :
    (I.modules.obj M).val.obj (G.op.obj V) :=
  (I.moduleUnderlying.inv.app M).hom.app (G.op.obj V)
    (AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G
      ((underlying.{u + 1, u, u + 1} J R).obj M) V x)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem kanModuleSection_map
    {C C' : Type (u + 1)} [Category.{u} C] [Category.{u} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [HasWeakSheafify J' (Type (u + 1))]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} C']
    (G : C ⥤ C') [G.IsContinuous J J']
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf J' CommRingCat.{u + 1})
    (I : SheafOfModules.AlgebraicInverseImage
      (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) J J') R S)
    {M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R} (f : M ⟶ N)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (I.modules.map f).val.app (G.op.obj V) (kanModuleSection J J' G R S I M V x) =
      kanModuleSection J J' G R S I N V (f.val.app V x) := by
  have hn := congrArg (fun k ↦ k.hom.app (G.op.obj V)
    (AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G
      ((underlying.{u + 1, u, u + 1} J R).obj M) V x))
    (I.moduleUnderlying.inv.naturality f)
  change (I.moduleUnderlying.inv.app N).hom.app (G.op.obj V)
    (((Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) J J').map
      ((underlying.{u + 1, u, u + 1} J R).map f)).hom.app (G.op.obj V) _) = _ at hn
  rw [kanSection_map] at hn
  exact hn.symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem kanCoefficient_one
    {C C' : Type (u + 1)} [Category.{u} C] [Category.{u} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [HasWeakSheafify J' (Type (u + 1))]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} C']
    (G : C ⥤ C') [G.IsContinuous J J']
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf J' CommRingCat.{u + 1})
    (I : SheafOfModules.AlgebraicInverseImage
      (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) J J') R S)
    (V : Cᵒᵖ) :
    I.ringUnderlying.hom.hom.app (G.op.obj V)
      (AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R) V (1 : R.obj.obj V)) =
      (1 : S.obj.obj (G.op.obj V)) := by
  let a := SheafOfModules.GeometricConstruction.ringOne R
  let Z := 𝟙_ (Sheaf J (Type (u + 1)))
  let t : Z.obj.obj V := PUnit.unit
  have h := I.ringOne Z a (fun _ _ ↦ rfl) (G.op.obj V)
    (AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G Z V t)
  rw [kanSection_map] at h
  exact h

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem inversePure_kanSection
    {C C' : Type (u + 1)} [Category.{u} C] [Category.{u} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [HasWeakSheafify J' (Type (u + 1))]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} C']
    (G : C ⥤ C') [G.IsContinuous J J']
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf J' CommRingCat.{u + 1})
    (I : SheafOfModules.AlgebraicInverseImage
      (Functor.sheafPullbackConstruction.sheafPullback G (Type (u + 1)) J J') R S)
    (mu : ∀ M N, I.modules.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
      ordinaryTensor.{u + 1, u, u + 1} J' S (I.modules.obj M) (I.modules.obj N))
    (hp : InverseTensorPure.{u + 1, u, u + 1} J J' _ R S I mu)
    (M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) :
    (mu M N).hom.val.app (G.op.obj V)
      (kanModuleSection J J' G R S I _ V
        (tensorSection.{u + 1, u, u + 1} J R M N V x y)) =
      tensorSection.{u + 1, u, u + 1} J' S (I.modules.obj M) (I.modules.obj N) (G.op.obj V)
        (kanModuleSection J J' G R S I M V x) (kanModuleSection J J' G R S I N V y) := by
  let Z := (underlying.{u + 1, u, u + 1} J R).obj M ⊗
    (underlying.{u + 1, u, u + 1} J R).obj N
  let z := SheafOfModules.CochainInversePairing.pureSheaf R M N
  have h := hp M N Z (CartesianMonoidalCategory.fst _ _)
    (CartesianMonoidalCategory.snd _ _) z (fun _ _ ↦ rfl) (G.op.obj V)
    (AlgebraicGeometry.ProEtale.spMonoidalInverseSection J J' G Z V (x, y))
  with_unfolding_all
    rw [kanSection_map J J' G z V (x, y),
      kanSection_map J J' G (CartesianMonoidalCategory.fst
        ((underlying.{u + 1, u, u + 1} J R).obj M)
        ((underlying.{u + 1, u, u + 1} J R).obj N)) V (x, y),
      kanSection_map J J' G (CartesianMonoidalCategory.snd
        ((underlying.{u + 1, u, u + 1} J R).obj M)
        ((underlying.{u + 1, u, u + 1} J R).obj N)) V (x, y)] at h
  exact h

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem pullbackTensorSummand_map
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
    {P P' Q Q' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℤ) (hpq : p + q = k) :
    tensorSummand.{c, v, r} J R P Q p q k hpq ≫
      ((totalTensor.{c, v, r} J R).map (Prod.mkHom f g)).f k =
    ordinaryTensorHom.{c, v, r} J R (f.f p) (g.f q) ≫
      tensorSummand.{c, v, r} J R P' Q' p q k hpq := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  change HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q k hpq ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _) (.up ℤ)).f k = _
  have hm : HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _) (.up ℤ) =
    HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ) := by
    simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  rw [hm, HomologicalComplex.ι_mapBifunctorMap]
  change (f.f p ▷ Q.X q) ≫ (P'.X p ◁ g.f q) ≫ _ =
    (f.f p ⊗ₘ g.f q) ≫ _
  rw [MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem pullbackSection_natural
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{u + 1} C]
    (R : Sheaf J CommRingCat.{u + 1})
    {M M' N N' : SemilinearSections.Mod.{u + 1, u, u + 1} J R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (ordinaryTensorHom.{u + 1, u, u + 1} J R f g).val.app U
      (tensorSection.{u + 1, u, u + 1} J R M N U x y) =
    tensorSection.{u + 1, u, u + 1} J R M' N' U (f.val.app U x) (g.val.app U y) := by
  with_unfolding_all exact SheafOfModules.pure_natural R f g U x y

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The given level comparison after the strict-system/sequence-site equivalence. -/
private def pullbackReductionLevel (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (n : ℕ) :
    spMonoidalOrdinary l E T D r ⋙
      SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n ≅
        (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.E :=
  Functor.isoWhiskerLeft r.ordinary
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D.equivalence.functor
        (SheafOfModules.strictSystemSequenceEquivalence
          (spCoefficientCommRings l E T)).unitIso.symm)
      (SheafOfModules.systemEvaluation (spCoefficientCommRings l E T) n)) ≪≫ r.level n

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem pullbackReduction_map_generator (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {M N : spIntegralSectionModules l E T}
    (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U) (x : M.val.obj U) :
    ((spMonoidalOrdinary l E T D r).map f).val.app (op (n, U.unop))
      (spMonoidalGenerator l E T D r M n U a x) =
      spMonoidalGenerator l E T D r N n U a (f.val.app U x) := by
  have hn := (r.level n).inv.naturality f
  have hh := congrArg (fun k ↦ k.val.app U
    (SheafOfModules.systemModelTmul
      (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model M U a x)) hn
  change _ = _ at hh
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hh
  exact hh.symm.trans (congrArg (((r.level n).inv.app N).val.app U)
    (SheafOfModules.systemScalarModel_map_tmul
      (D.scalar (spIntegralReductionScalar l E T r.coefficient n)) f U a x))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Scalar adjunction reduces equality to sheafified binary tensor generators. -/
private theorem pullbackReduction_tensor_ext (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (M N : spIntegralSectionModules l E T)
    (H : spMonoidalSystems l E T)
    (f g : (spMonoidalOrdinary l E T D r).obj (M ⊗ N) ⟶ H)
    (h : ∀ n U x y,
      f.val.app (op (n, U.unop)) (spMonoidalGenerator l E T D r _ n U 1
        (tensorSection.{u + 1, u, u + 1} _ _ M N U x y)) =
      g.val.app (op (n, U.unop)) (spMonoidalGenerator l E T D r _ n U 1
        (tensorSection.{u + 1, u, u + 1} _ _ M N U x y))) : f = g := by
  have hn (n : ℕ) :
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map f =
      (SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings l E T) n).map g := by
    apply (cancel_epi ((pullbackReductionLevel l E T D r n).inv.app (M ⊗ N))).1
    apply ((D.scalar (spIntegralReductionScalar l E T r.coefficient n)).ordinaryAdj.homEquiv
      _ _).injective
    apply SheafOfModules.tensor_ext (spIntegralSectionRing l E T) M N
    intro U x y
    simp only [Adjunction.homEquiv_unit, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    let S := D.scalar (spIntegralReductionScalar l E T r.coefficient n)
    have hu := S.unit_normalized (M ⊗ N) U
      (tensorSection.{u + 1, u, u + 1} _ _ M N U x y)
    have hf := congrArg (fun v ↦ f.val.app (op (n, U.unop))
      (((r.level n).inv.app (M ⊗ N)).val.app U v)) hu
    have hg := congrArg (fun v ↦ g.val.app (op (n, U.unop))
      (((r.level n).inv.app (M ⊗ N)).val.app U v)) hu
    with_unfolding_all exact hf.trans ((h n U x y).trans hg.symm)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rcases V with ⟨n, U⟩
  exact congrArg (fun k ↦ k.val.app (op U)) (hn n)

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The normalized module transpose detects maps on pulled reduction tensor generators. -/
private theorem pullbackReductionTensor_ext
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (p : SpReductionPullbackTower l E T D r g D' r')
    (M N : spIntegralSectionModules l E T) (H : spMonoidalSystems l E T')
    (f k : p.system.modules.obj ((spMonoidalOrdinary l E T D r).obj
      (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) M N)) ⟶ H)
    (hfg : ∀ n V x y,
      f.val.app (op (n, (Scheme.proEtaleBaseChange g).obj V.unop))
        (spMonoidalSystemPullSection l E T g p.system _ (op (n, V.unop))
          (spMonoidalGenerator l E T D r _ n V 1
            (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              (spIntegralSectionRing l E T) M N V x y))) =
      k.val.app (op (n, (Scheme.proEtaleBaseChange g).obj V.unop))
        (spMonoidalSystemPullSection l E T g p.system _ (op (n, V.unop))
          (spMonoidalGenerator l E T D r _ n V 1
            (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              (spIntegralSectionRing l E T) M N V x y)))) : f = k := by
  obtain ⟨hc, _, hlim⟩ := spMonoidalSequenceInverseImage_leftExact g
  letI := hc
  letI := hlim
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)) (Type (u + 1))
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
  obtain ⟨P, e, he⟩ := inverseLinearMate.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T')
    (spMonoidalSequenceInverseImage T g) _ adj p.system H
  obtain ⟨mate, hE⟩ := he ((spMonoidalOrdinary l E T D r).obj
    (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) M N))
  apply mate.injective
  apply pullbackReduction_tensor_ext l E T D r M N P (mate f) (mate k)
  intro n V x y
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op (n, V.unop)))).1
  let z := spMonoidalGenerator l E T D r _ n V 1
    (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) M N V x y)
  have hf := congrArg (fun a ↦ a.hom.app (op (n, V.unop)) z) (hE f)
  have hk := congrArg (fun a ↦ a.hom.app (op (n, V.unop)) z) (hE k)
  simp only [Adjunction.homEquiv_unit] at hf hk
  with_unfolding_all exact hf.trans ((hfg n V x y).trans hk.symm)

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Check the ordinary square on pulled tensors with coefficient one. -/
private theorem reductionOrdinarySquare
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (M : SpReductionMonoidalTower l E T D r)
    {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (M' : SpReductionMonoidalTower l E T' D' r')
    (p : SpReductionPullbackTower l E T D r g D' r')
    (iOrd : ∀ X Y : spIntegralSectionModules l E T,
      p.integral.modules.obj (ordinaryTensor.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) X Y) ≅
      ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T')
        (spIntegralSectionRing l E T') (p.integral.modules.obj X) (p.integral.modules.obj Y))
    (hi : InverseTensorPure.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (spIntegralSectionRing l E T) (spIntegralSectionRing l E T') p.integral iOrd)
    (sOrd : ∀ X Y : spMonoidalSystems l E T,
      p.system.modules.obj (ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (spMonoidalSystemRing l E T) X Y) ≅
      ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T'))
        (spMonoidalSystemRing l E T') (p.system.modules.obj X) (p.system.modules.obj Y))
    (hs : InverseTensorPure.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSequenceTopology (Scheme.ProEt.topology T'))
      (spMonoidalSequenceInverseImage T g)
      (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T') p.system sOrd)
    (X Y : spIntegralSectionModules l E T) :
    (spMonoidalOrdinary l E T' D' r').map (iOrd X Y).hom ≫
      (M'.ordinary (p.integral.modules.obj X) (p.integral.modules.obj Y)).hom ≫
      ordinaryTensorHom.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T')) (spMonoidalSystemRing l E T')
        (p.ordinary.hom.app X) (p.ordinary.hom.app Y) =
    p.ordinary.hom.app (ordinaryTensor.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) X Y) ≫
      p.system.modules.map (M.ordinary X Y).hom ≫
      (sOrd ((spMonoidalOrdinary l E T D r).obj X)
        ((spMonoidalOrdinary l E T D r).obj Y)).hom := by
  obtain ⟨hc, _, hlim⟩ := spMonoidalSequenceInverseImage_leftExact g
  letI := hc
  apply (cancel_epi (p.ordinary.inv.app (ordinaryTensor.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) X Y))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply pullbackReductionTensor_ext l E T D r g D' r' p X Y
  intro n V x y
  let V' := (Scheme.proEtaleBaseChange g).op.obj V
  have h1 : spMonoidalPullCoefficient T g (p.level n) V 1 = 1 :=
    kanCoefficient_one (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
      (Scheme.proEtaleBaseChange g)
      (((spCoefficientCommRings.{u, u} l E T).obj (op n)))
      (((spCoefficientCommRings.{u, u} l E T').obj (op n))) (p.level n) V
  have hpi : (iOrd X Y).hom.val.app V'
      (spMonoidalPullSection T g p.integral _ V
        (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (spIntegralSectionRing l E T) X Y V x y)) =
      tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T')
        (spIntegralSectionRing l E T') _ _ V'
        (spMonoidalPullSection T g p.integral X V x)
        (spMonoidalPullSection T g p.integral Y V y) :=
    inversePure_kanSection (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
      (Scheme.proEtaleBaseChange g) (spIntegralSectionRing l E T)
      (spIntegralSectionRing l E T') p.integral iOrd hi X Y V x y
  have hpgen (L : spIntegralSectionModules l E T) (z : L.val.obj V) :
      (p.ordinary.hom.app L).val.app (op (n, V'.unop))
        (spMonoidalGenerator l E T' D' r' (p.integral.modules.obj L) n V' 1
          (spMonoidalPullSection T g p.integral L V z)) =
      spMonoidalSystemPullSection l E T g p.system
        ((spMonoidalOrdinary l E T D r).obj L) (op (n, V.unop))
        (spMonoidalGenerator l E T D r L n V 1 z) := by
    have h := p.ordinary_section L n V z 1
    rw [h1] at h
    have h' := congrArg ((p.ordinary.hom.app L).val.app (op (n, V'.unop))) h
    have hid := congrArg (fun a ↦ a.val.app (op (n, V'.unop))
      (spMonoidalSystemPullSection l E T g p.system
        ((spMonoidalOrdinary l E T D r).obj L) (op (n, V.unop))
        (spMonoidalGenerator l E T D r L n V 1 z))) (p.ordinary.inv_hom_id_app L)
    exact h'.symm.trans hid
  have hmap (L N : spMonoidalSystems l E T) (f : L ⟶ N)
      (z : L.val.obj (op (n, V.unop))) :
      (p.system.modules.map f).val.app (op (n, V'.unop))
        (spMonoidalSystemPullSection l E T g p.system L (op (n, V.unop)) z) =
      spMonoidalSystemPullSection l E T g p.system N (op (n, V.unop))
        (f.val.app (op (n, V.unop)) z) :=
    kanModuleSection_map (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSequenceTopology (Scheme.ProEt.topology T'))
      ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g))
      (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T') p.system f _ z
  have hps := inversePure_kanSection
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g))
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T') p.system sOrd hs
    ((spMonoidalOrdinary l E T D r).obj X) ((spMonoidalOrdinary l E T D r).obj Y)
    (op (n, V.unop)) (spMonoidalGenerator l E T D r X n V 1 x)
      (spMonoidalGenerator l E T D r Y n V 1 y)
  have hbase := p.ordinary_section
    (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) X Y) n V
    (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) X Y V x y) 1
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  with_unfolding_all
    erw [hbase, h1, pullbackReduction_map_generator, hpi, M'.forward,
      pullbackSection_natural, hpgen, hpgen, hmap, M.forward]
  exact hps.symm


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The actual counit remains invertible after the sequence-site equivalence. -/
private theorem pullbackReductionCounit_isIso (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    IsIso ((spMonoidalCounit l E T D r).app P) := by
  let := D.hasDerived
  let := r.computes P hP
  dsimp only [spMonoidalCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem reductionInverseNormalization
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (M : SpReductionMonoidalTower l E T D r)
    (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) P)
    (fQ : flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) Q) :
    M.μ.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (spMonoidalReduction l E T D r).map
        (tensorModelIso.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (spIntegralSectionRing l E T) M.source M.sourceModel P Q hP hQ).inv ≫
      (spMonoidalCounit l E T D r).app ((spMonoidalIntegralTotal l E T).obj (P, Q)) =
    M.target.tensor.map (Prod.mkHom ((spMonoidalCounit l E T D r).app P)
      ((spMonoidalCounit l E T D r).app Q)) ≫
      (tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (spMonoidalSystemRing l E T) M.target M.targetModel
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj Q)
        (M.system_kflat P hP fP) (M.system_kflat Q hQ fQ)).inv ≫
      DerivedCategory.Q.map (M.chain.hom.app (P, Q)) := by
  letI := pullbackReductionCounit_isIso l E T D r P hP
  letI := pullbackReductionCounit_isIso l E T D r Q hQ
  letI := pullbackReductionCounit_isIso l E T D r
    ((spMonoidalIntegralTotal l E T).obj (P, Q)) (M.total_kflat P Q hP hQ fP fQ).1
  exact invertTensorEquation
    ((spMonoidalReduction l E T D r).mapIso
      (tensorModelIso.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) M.source M.sourceModel P Q hP hQ))
    (M.μ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (M.target.tensor.mapIso
      ((asIso ((spMonoidalCounit l E T D r).app P)).prod
        (asIso ((spMonoidalCounit l E T D r).app Q))))
    (asIso ((spMonoidalCounit l E T D r).app ((spMonoidalIntegralTotal l E T).obj (P, Q))))
    (DerivedCategory.Q.mapIso (M.chain.app (P, Q)))
    (tensorModelIso.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T) M.target M.targetModel _ _
      (M.system_kflat P hP fP) (M.system_kflat Q hQ fQ)) (M.derived P Q hP hQ fP fQ)

section ReductionSquare
set_option quotPrecheck false
variable (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
  (M : SpReductionMonoidalTower l E T D r)
  {T' : Scheme.{u}} (g : T' ⟶ T)
  (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
  (M' : SpReductionMonoidalTower l E T' D' r')
  (p : SpReductionPullbackTower l E T D r g D' r')
  (iTensor : M.source.tensor ⋙ p.integral.modules.mapDerivedCategory ≅
    (p.integral.modules.mapDerivedCategory.prod p.integral.modules.mapDerivedCategory) ⋙
      M'.source.tensor)
  (sTensor : M.target.tensor ⋙ p.system.modules.mapDerivedCategory ≅
    (p.system.modules.mapDerivedCategory.prod p.system.modules.mapDerivedCategory) ⋙
      M'.target.tensor)
  (iModel : TensorComparisonModel.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T') p.integral.modules
    M.source M'.source M.sourceModel M'.sourceModel iTensor)
  (sModel : TensorComparisonModel.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T') p.system.modules
    M.target M'.target M.targetModel M'.targetModel sTensor)
  (hi : InverseTensorPure.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
    (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T') p.integral iModel.ordinary)
  (hs : InverseTensorPure.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    (spMonoidalSequenceInverseImage T g)
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T') p.system sModel.ordinary)

local notation "J₀" => Scheme.ProEt.topology T
local notation "J₁" => Scheme.ProEt.topology T'
local notation "J₂" => coefficientSequenceTopology (Scheme.ProEt.topology T)
local notation "J₃" => coefficientSequenceTopology (Scheme.ProEt.topology T')
local notation "R₀" => spIntegralSectionRing l E T
local notation "R₁" => spIntegralSectionRing l E T'
local notation "R₂" => spMonoidalSystemRing l E T
local notation "R₃" => spMonoidalSystemRing l E T'
local notation "F" => p.integral.modules
local notation "G" => spMonoidalOrdinary l E T' D' r'
local notation "H" => spMonoidalOrdinary l E T D r
local notation "I" => p.system.modules
local notation "FD" => p.integral.modules.mapDerivedCategory
local notation "GD" => spMonoidalReduction l E T' D' r'
local notation "HD" => spMonoidalReduction l E T D r
local notation "ID" => p.system.modules.mapDerivedCategory
local notation "S₀" => M.source
local notation "S₁" => M'.source
local notation "S₂" => M.target
local notation "S₃" => M'.target
local notation "T₀" => M.sourceModel
local notation "T₁" => M'.sourceModel
local notation "T₂" => M.targetModel
local notation "T₃" => M'.targetModel

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
include hi hs in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Totalization of the ordinary square, checked on each signed bidegree summand. -/
private theorem reductionCochainSquare
    (P Q : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1} J₀ R₀) ℤ) :
    M'.chain.hom.app ((((F).mapHomologicalComplex (.up ℤ)).obj P),
        (((F).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      ((G).mapHomologicalComplex (.up ℤ)).map (iModel.chain P Q) ≫
      (NatTrans.mapHomologicalComplex p.ordinary.hom (.up ℤ)).app
        ((totalTensor.{u + 1, u, u + 1} J₀ R₀).obj (P, Q)) =
    (totalTensor.{u + 1, u, u + 1} J₃ R₃).map
        (Prod.mkHom ((NatTrans.mapHomologicalComplex p.ordinary.hom (.up ℤ)).app P)
          ((NatTrans.mapHomologicalComplex p.ordinary.hom (.up ℤ)).app Q)) ≫
      sModel.chain (((H).mapHomologicalComplex (.up ℤ)).obj P)
        (((H).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      ((I).mapHomologicalComplex (.up ℤ)).map (M.chain.hom.app (P, Q)) := by
  let θ := p.ordinary
  have ho := reductionOrdinarySquare l E T D r M g D' r' M' p
    iModel.ordinary hi sModel.ordinary hs
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₃
  let := SheafOfModules.monoidalCategory R₃
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R₃
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R₃
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change tensorSummand.{u + 1, u, u + 1} J₃ R₃ _ _ p q k hpq ≫ _ =
    tensorSummand.{u + 1, u, u + 1} J₃ R₃ _ _ p q k hpq ≫ _
  erw [reassoc_of% (M'.summand (((F).mapHomologicalComplex (.up ℤ)).obj P)
    (((F).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq)]
  have hsF := congrArg (G).map (iModel.summand P Q p q k hpq)
  simp only [(G).map_comp] at hsF
  erw [reassoc_of% hsF]
  have hn := θ.hom.naturality (tensorSummand.{u + 1, u, u + 1} J₀ R₀ P Q p q k hpq)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  erw [reassoc_of% (pullbackTensorSummand_map.{u + 1, u, u + 1} J₃ R₃
    ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app Q) p q k hpq)]
  conv_rhs => erw [reassoc_of% (sModel.summand (((H).mapHomologicalComplex (.up ℤ)).obj P)
    (((H).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq)]
  have hsH := congrArg (I).map (M.summand P Q p q k hpq)
  simp only [(I).map_comp] at hsH
  erw [hsH]
  change (M'.ordinary ((F).obj (P.X p)) ((F).obj (Q.X q))).inv ≫
      (G).map (iModel.ordinary (P.X p) (Q.X q)).inv ≫
      θ.hom.app (ordinaryTensor.{u + 1, u, u + 1} J₀ R₀ (P.X p) (Q.X q)) ≫
      (I).map ((H).map (tensorSummand.{u + 1, u, u + 1} J₀ R₀ P Q p q k hpq)) =
    ordinaryTensorHom.{u + 1, u, u + 1} J₃ R₃ (θ.hom.app (P.X p)) (θ.hom.app (Q.X q)) ≫
      (sModel.ordinary ((H).obj (P.X p)) ((H).obj (Q.X q))).inv ≫
      (I).map (M.ordinary (P.X p) (Q.X q)).inv ≫
      (I).map ((H).map (tensorSummand.{u + 1, u, u + 1} J₀ R₀ P Q p q k hpq))
  let u := (G).mapIso (iModel.ordinary (P.X p) (Q.X q)) ≪≫
    M'.ordinary ((F).obj (P.X p)) ((F).obj (Q.X q))
  let w := (I).mapIso (M.ordinary (P.X p) (Q.X q)) ≪≫
    sModel.ordinary ((H).obj (P.X p)) ((H).obj (Q.X q))
  have hi : u.inv ≫ θ.hom.app (ordinaryTensor.{u + 1, u, u + 1} J₀ R₀ (P.X p) (Q.X q)) =
      ordinaryTensorHom.{u + 1, u, u + 1} J₃ R₃ (θ.hom.app (P.X p)) (θ.hom.app (Q.X q)) ≫
        w.inv := by
    apply (Iso.inv_comp_eq u).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv w).2
    exact (ho (P.X p) (Q.X q)).symm
  simpa only [u, w, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using
    congrArg (fun f ↦ f ≫
      (I).map ((H).map (tensorSummand.{u + 1, u, u + 1} J₀ R₀ P Q p q k hpq))) hi

local notation "FC" => (F).mapHomologicalComplex (.up ℤ)
local notation "GC" => (G).mapHomologicalComplex (.up ℤ)
local notation "HC" => (H).mapHomologicalComplex (.up ℤ)
local notation "IC" => (I).mapHomologicalComplex (.up ℤ)
local notation "Ord" => NatIso.mapHomologicalComplex p.ordinary (.up ℤ)
local notation "c₀" => spMonoidalCounit l E T D r
local notation "c₁" => spMonoidalCounit l E T' D' r'

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[irreducible] private def integralCompositeFactor
    (P : CochainComplex (spIntegralSectionModules l E T) ℤ) :
    (GD).obj ((FD).obj (DerivedCategory.Q.obj P)) ⟶ DerivedCategory.Q.obj ((GC).obj ((FC).obj P)) :=
  (GD).map ((F).mapDerivedCategoryFactors.hom.app P) ≫ (c₁).app ((FC).obj P)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
@[irreducible] private def systemCompositeFactor
    (P : CochainComplex (spIntegralSectionModules l E T) ℤ) :
    (ID).obj ((HD).obj (DerivedCategory.Q.obj P)) ⟶ DerivedCategory.Q.obj ((IC).obj ((HC).obj P)) :=
  (ID).map ((c₀).app P) ≫ (I).mapDerivedCategoryFactors.hom.app ((HC).obj P)

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
include iModel in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem inverseImageFlatTerms
    (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (fP : flatTerms.{u + 1, u, u + 1} J₀ R₀ P) :
    (flatTerms.{u + 1, u, u + 1} J₁ R₁) ((FC).obj P) := by
  intro n
  exact tensorComparisonModel_preserves_flat.{u + 1, u, u + 1} J₀ J₁ R₀ R₁ F
    S₀ S₁ T₀ T₁ iTensor iModel (P.X n) (fP n)

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
include iModel in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem systemCompositeKflat
    (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (fP : (flatTerms.{u + 1, u, u + 1} J₀ R₀) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J₃) (R := R₃)
      ((IC).obj ((HC).obj P)) := by
  exact SheafOfModules.kFlat_iso_independent R₃ ((Ord).app P)
    (M'.system_kflat ((FC).obj P) (iModel.kflat P hP fP)
      (inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel P fP))


set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Normalize the composite of integral inverse image followed by reduction. -/
private theorem integralCompositeNormalization
    (iFull : FullTensorNormalization.{u + 1, u, u + 1} J₀ J₁ R₀ R₁ F
      S₀ S₁ T₀ T₁ iTensor iModel)
    (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{u + 1, u, u + 1} J₀ R₀ P)
    (fQ : flatTerms.{u + 1, u, u + 1} J₀ R₀ Q) :
    M'.μ.inv.app ((FD).obj (DerivedCategory.Q.obj P), (FD).obj (DerivedCategory.Q.obj Q)) ≫
      (GD).map (iTensor.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (GD).map ((FD).map (tensorModelIso.{u + 1, u, u + 1} J₀ R₀ S₀ T₀ P Q hP hQ).inv) ≫
      integralCompositeFactor l E T D r g D' r' p
        ((totalTensor.{u + 1, u, u + 1} J₀ R₀).obj (P, Q)) =
    (S₃).tensor.map (Prod.mkHom (integralCompositeFactor l E T D r g D' r' p P)
      (integralCompositeFactor l E T D r g D' r' p Q)) ≫
      (tensorModelIso.{u + 1, u, u + 1} J₃ R₃ S₃ T₃ ((GC).obj ((FC).obj P)) ((GC).obj ((FC).obj Q))
        (M'.system_kflat _ (iModel.kflat P hP fP)
          (inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel P fP))
        (M'.system_kflat _ (iModel.kflat Q hQ fQ)
          (inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel Q fQ))).inv ≫
      DerivedCategory.Q.map (M'.chain.hom.app ((FC).obj P, (FC).obj Q) ≫
        (GC).map (iModel.chain P Q)) := by
  let FP := (FC).obj P
  let FQ := (FC).obj Q
  have ffP := inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel P fP
  have ffQ := inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel Q fQ
  have hF := iFull P Q hP hQ (iModel.kflat P hP fP) (iModel.kflat Q hQ fQ)
  have hG := reductionInverseNormalization l E T' D' r' M' FP FQ
    (iModel.kflat P hP fP) (iModel.kflat Q hQ fQ) ffP ffQ
  have hn := M'.μ.inv.naturality (Prod.mkHom ((F).mapDerivedCategoryFactors.hom.app P)
    ((F).mapDerivedCategoryFactors.hom.app Q))
  change (S₃).tensor.map (Prod.mkHom ((GD).map ((F).mapDerivedCategoryFactors.hom.app P))
      ((GD).map ((F).mapDerivedCategoryFactors.hom.app Q))) ≫
      M'.μ.inv.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) =
    M'.μ.inv.app ((FD).obj (DerivedCategory.Q.obj P), (FD).obj (DerivedCategory.Q.obj Q)) ≫
      (GD).map ((S₁).tensor.map (Prod.mkHom ((F).mapDerivedCategoryFactors.hom.app P)
        ((F).mapDerivedCategoryFactors.hom.app Q))) at hn
  simp only [integralCompositeFactor]
  rw [← (GD).map_comp_assoc, ← (GD).map_comp_assoc]
  simp only [Category.assoc]
  rw [hF]
  simp only [(GD).map_comp, Category.assoc]
  with_unfolding_all erw [← reassoc_of% hn]
  have hg := (c₁).naturality (iModel.chain P Q)
  dsimp only [Functor.comp_map] at hg
  erw [hg]
  with_unfolding_all
    erw [reassoc_of% hG]
    simp only [← (S₃).tensor.map_comp_assoc, prod_comp, DerivedCategory.Q.map_comp]
    rfl

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Normalize the composite of reduction followed by system inverse image. -/
private theorem systemCompositeNormalization
    (sFull : FullTensorNormalization.{u + 1, u, u + 1} J₂ J₃ R₂ R₃ I
      S₂ S₃ T₂ T₃ sTensor sModel)
    (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{u + 1, u, u + 1} J₀ R₀ P)
    (fQ : flatTerms.{u + 1, u, u + 1} J₀ R₀ Q) :
    sTensor.inv.app ((HD).obj (DerivedCategory.Q.obj P), (HD).obj (DerivedCategory.Q.obj Q)) ≫
      (ID).map (M.μ.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (ID).map ((HD).map (tensorModelIso.{u + 1, u, u + 1} J₀ R₀ S₀ T₀ P Q hP hQ).inv) ≫
      systemCompositeFactor l E T D r g D' r' p
        ((totalTensor.{u + 1, u, u + 1} J₀ R₀).obj (P, Q)) =
    (S₃).tensor.map (Prod.mkHom (systemCompositeFactor l E T D r g D' r' p P)
      (systemCompositeFactor l E T D r g D' r' p Q)) ≫
      (tensorModelIso.{u + 1, u, u + 1} J₃ R₃ S₃ T₃ ((IC).obj ((HC).obj P)) ((IC).obj ((HC).obj Q))
        (systemCompositeKflat l E T D r M g D' r' M' p iTensor iModel P hP fP)
        (systemCompositeKflat l E T D r M g D' r' M' p iTensor iModel Q hQ fQ)).inv ≫
      DerivedCategory.Q.map (sModel.chain ((HC).obj P) ((HC).obj Q) ≫
        (IC).map (M.chain.hom.app (P, Q))) := by
  let HP := (HC).obj P
  let HQ := (HC).obj Q
  have hF := reductionInverseNormalization l E T D r M P Q hP hQ fP fQ
  have hG := sFull HP HQ (M.system_kflat P hP fP) (M.system_kflat Q hQ fQ)
    (systemCompositeKflat l E T D r M g D' r' M' p iTensor iModel P hP fP)
    (systemCompositeKflat l E T D r M g D' r' M' p iTensor iModel Q hQ fQ)
  have hn := sTensor.inv.naturality (Prod.mkHom ((c₀).app P) ((c₀).app Q))
  change (S₃).tensor.map (Prod.mkHom ((ID).map ((c₀).app P)) ((ID).map ((c₀).app Q))) ≫
      sTensor.inv.app (DerivedCategory.Q.obj HP, DerivedCategory.Q.obj HQ) =
    sTensor.inv.app ((HD).obj (DerivedCategory.Q.obj P), (HD).obj (DerivedCategory.Q.obj Q)) ≫
      (ID).map ((S₂).tensor.map (Prod.mkHom ((c₀).app P) ((c₀).app Q))) at hn
  simp only [systemCompositeFactor]
  rw [← (ID).map_comp_assoc, ← (ID).map_comp_assoc]
  simp only [Category.assoc]
  rw [hF]
  simp only [(ID).map_comp, Category.assoc]
  with_unfolding_all erw [← reassoc_of% hn]
  have hg := (I).mapDerivedCategoryFactors.hom.naturality (M.chain.hom.app (P, Q))
  dsimp only [Functor.comp_map] at hg
  erw [hg]
  with_unfolding_all
    erw [reassoc_of% hG]
    simp only [← (S₃).tensor.map_comp_assoc, prod_comp, DerivedCategory.Q.map_comp]
    rfl

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
include hi hs in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Compare the two inverse tensorators using the three normalized square equations. -/
private theorem reductionInverseOnRepresentatives
    (iFull : FullTensorNormalization.{u + 1, u, u + 1} J₀ J₁ R₀ R₁ F
      S₀ S₁ T₀ T₁ iTensor iModel)
    (sFull : FullTensorNormalization.{u + 1, u, u + 1} J₂ J₃ R₂ R₃ I
      S₂ S₃ T₂ T₃ sTensor sModel)
    (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{u + 1, u, u + 1} J₀ R₀ P)
    (fQ : flatTerms.{u + 1, u, u + 1} J₀ R₀ Q) :
    (S₃).tensor.map (Prod.mkHom (p.ν.hom.app (DerivedCategory.Q.obj P))
        (p.ν.hom.app (DerivedCategory.Q.obj Q))) ≫
      sTensor.inv.app ((HD).obj (DerivedCategory.Q.obj P), (HD).obj (DerivedCategory.Q.obj Q)) ≫
      (ID).map (M.μ.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
    M'.μ.inv.app ((FD).obj (DerivedCategory.Q.obj P), (FD).obj (DerivedCategory.Q.obj Q)) ≫
      (GD).map (iTensor.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      p.ν.hom.app ((S₀).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let d := (Ord).hom
  let FP := (FC).obj P
  let FQ := (FC).obj Q
  let HP := (HC).obj P
  let HQ := (HC).obj Q
  let GFP := (GC).obj FP
  let GFQ := (GC).obj FQ
  let IHP := (IC).obj HP
  let IHQ := (IC).obj HQ
  let Tot := (totalTensor.{u + 1, u, u + 1} J₀ R₀).obj (P, Q)
  let bFG := integralCompositeFactor l E T D r g D' r' p
  let bHI := systemCompositeFactor l E T D r g D' r' p
  let r₀ := tensorModelIso.{u + 1, u, u + 1} J₀ R₀ S₀ T₀ P Q hP hQ
  have ffP := inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel P fP
  have ffQ := inverseImageFlatTerms l E T D r M g D' r' M' p iTensor iModel Q fQ
  have hkGFP := M'.system_kflat FP (iModel.kflat P hP fP) ffP
  have hkGFQ := M'.system_kflat FQ (iModel.kflat Q hQ fQ) ffQ
  have hkIHP := systemCompositeKflat l E T D r M g D' r' M' p iTensor iModel P hP fP
  have hkIHQ := systemCompositeKflat l E T D r M g D' r' M' p iTensor iModel Q hQ fQ
  let rFG := tensorModelIso.{u + 1, u, u + 1} J₃ R₃ S₃ T₃ GFP GFQ hkGFP hkGFQ
  let rHI := tensorModelIso.{u + 1, u, u + 1} J₃ R₃ S₃ T₃ IHP IHQ hkIHP hkIHQ
  let cFG := M'.chain.hom.app (FP, FQ) ≫ (GC).map (iModel.chain P Q)
  let cHI := sModel.chain HP HQ ≫ (IC).map (M.chain.hom.app (P, Q))
  have hFG := integralCompositeNormalization l E T D r M g D' r' M' p
    iTensor iModel iFull P Q hP hQ fP fQ
  have hHI := systemCompositeNormalization l E T D r M g D' r' M' p
    iTensor sTensor iModel sModel sFull P Q hP hQ fP fQ
  change _ = (S₃).tensor.map (Prod.mkHom (bFG P) (bFG Q)) ≫
    rFG.inv ≫ DerivedCategory.Q.map cFG at hFG
  change _ = (S₃).tensor.map (Prod.mkHom (bHI P) (bHI Q)) ≫
    rHI.inv ≫ DerivedCategory.Q.map cHI at hHI
  have hp : p.ν.hom.app (DerivedCategory.Q.obj P) ≫ bHI P =
      bFG P ≫ DerivedCategory.Q.map (d.app P) := by
    simpa only [bFG, bHI, integralCompositeFactor, systemCompositeFactor, Category.assoc]
      using (p.derived P hP fP).symm
  have hq : p.ν.hom.app (DerivedCategory.Q.obj Q) ≫ bHI Q =
      bFG Q ≫ DerivedCategory.Q.map (d.app Q) := by
    simpa only [bFG, bHI, integralCompositeFactor, systemCompositeFactor, Category.assoc]
      using (p.derived Q hQ fQ).symm
  have hTot := M.total_kflat P Q hP hQ fP fQ
  have ht : p.ν.hom.app (DerivedCategory.Q.obj Tot) ≫ bHI Tot =
      bFG Tot ≫ DerivedCategory.Q.map (d.app Tot) :=
    by simpa only [bFG, bHI, integralCompositeFactor, systemCompositeFactor, Category.assoc]
      using (p.derived Tot hTot.1 hTot.2).symm
  have hn : DerivedCategory.Q.map ((totalTensor.{u + 1, u, u + 1} J₃ R₃).map
      (Prod.mkHom (d.app P) (d.app Q))) ≫ rHI.hom =
    rFG.hom ≫ (S₃).tensor.map (Prod.mkHom (DerivedCategory.Q.map (d.app P))
      (DerivedCategory.Q.map (d.app Q))) := by
    let ρ : ObjectProperty (CochainComplex (spMonoidalSystems l E T') ℤ) :=
      CochainComplex.IsKFlatIndependentCoefficients (J := J₃) (R := R₃)
    let f' : (⟨GFP, hkGFP⟩ : ρ.FullSubcategory) ⟶ ⟨IHP, hkIHP⟩ :=
      ObjectProperty.homMk (d.app P)
    let g' : (⟨GFQ, hkGFQ⟩ : ρ.FullSubcategory) ⟶ ⟨IHQ, hkIHQ⟩ :=
      ObjectProperty.homMk (d.app Q)
    exact (T₃).comparison.hom.naturality (Prod.mkHom f' g')
  have hinv := congrArg (fun f ↦ rFG.inv ≫ f ≫ rHI.inv) hn
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
    Category.comp_id] at hinv
  have hc := reductionCochainSquare l E T D r M g D' r' M' p
    iTensor sTensor iModel sModel hi hs P Q
  change cFG ≫ d.app Tot =
    (totalTensor.{u + 1, u, u + 1} J₃ R₃).map
      (Prod.mkHom (d.app P) (d.app Q)) ≫ cHI at hc
  letI := pullbackReductionCounit_isIso l E T D r Tot hTot.1
  letI : IsIso (bHI Tot) := by
    with_unfolding_all
      change IsIso ((ID).map ((c₀).app Tot) ≫
        (I).mapDerivedCategoryFactors.hom.app ((HC).obj Tot))
    infer_instance
  let z := (ID).mapIso ((HD).mapIso r₀.symm) ≪≫ asIso (bHI Tot)
  apply (cancel_mono z.hom).1
  simp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  have hδ := p.ν.hom.naturality r₀.inv
  change (GD).map ((FD).map r₀.inv) ≫ p.ν.hom.app (DerivedCategory.Q.obj Tot) =
    p.ν.hom.app ((S₀).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (ID).map ((HD).map r₀.inv) at hδ
  erw [← reassoc_of% hδ]
  erw [ht]
  erw [reassoc_of% hFG]
  erw [hHI]
  rw [← (S₃).tensor.map_comp_assoc]
  simp only [prod_comp]
  erw [hp, hq]
  erw [← prod_comp (Prod.mkHom (bFG P) (bFG Q))
    (Prod.mkHom (DerivedCategory.Q.map (d.app P)) (DerivedCategory.Q.map (d.app Q))),
    (S₃).tensor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hinv]
  simp only [← DerivedCategory.Q.map_comp, ← Category.assoc]
  erw [← hc]

set_option maxHeartbeats 2000000 in
-- Independent endpoint models make the normalization expressions large.
include hi hs in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Two-variable localization extends the representative square to all derived objects. -/
private theorem reductionTensorSquare
    (iFull : FullTensorNormalization.{u + 1, u, u + 1} J₀ J₁ R₀ R₁ F
      S₀ S₁ T₀ T₁ iTensor iModel)
    (sFull : FullTensorNormalization.{u + 1, u, u + 1} J₂ J₃ R₂ R₃ I
      S₂ S₃ T₂ T₃ sTensor sModel)
    (X Y : DerivedCategory (spIntegralSectionModules l E T)) :
    (GD).map (iTensor.hom.app (X, Y)) ≫ M'.μ.hom.app ((FD).obj X, (FD).obj Y) ≫
      (S₃).tensor.map (Prod.mkHom (p.ν.hom.app X) (p.ν.hom.app Y)) =
    p.ν.hom.app ((S₀).tensor.obj (X, Y)) ≫ (ID).map (M.μ.hom.app (X, Y)) ≫
      sTensor.hom.app ((HD).obj X, (HD).obj Y) := by
  let U : ((FD).prod FD) ⋙ ((GD).prod GD) ⋙ (S₃).tensor ⟶ (S₀).tensor ⋙ HD ⋙ ID :=
    Functor.whiskerRight (p.ν.hom.prod p.ν.hom) (S₃).tensor ≫
      Functor.whiskerLeft ((HD).prod HD) sTensor.inv ≫
      Functor.whiskerRight M.μ.inv ID
  let V : ((FD).prod FD) ⋙ ((GD).prod GD) ⋙ (S₃).tensor ⟶ (S₀).tensor ⋙ HD ⋙ ID :=
    Functor.whiskerLeft ((FD).prod FD) M'.μ.inv ≫
      Functor.whiskerRight iTensor.inv GD ≫ Functor.whiskerLeft (S₀).tensor p.ν.hom
  have he : U = V := by
    obtain ⟨_, _, _, h⟩ := SheafOfModules.cochain_tensor_model_rigidity J₀ R₀
    apply (h (SemilinearSections.D.{u + 1, u, u + 1} J₃ R₃) inferInstance _ _).1
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    exact reductionInverseOnRepresentatives l E T D r M g D' r' M' p
      iTensor sTensor iModel sModel hi hs iFull sFull
      P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hi' := congrArg (fun t ↦ t.app (X, Y)) he
  change (S₃).tensor.map (Prod.mkHom (p.ν.hom.app X) (p.ν.hom.app Y)) ≫
      sTensor.inv.app ((HD).obj X, (HD).obj Y) ≫ (ID).map (M.μ.inv.app (X, Y)) =
    M'.μ.inv.app ((FD).obj X, (FD).obj Y) ≫ (GD).map (iTensor.inv.app (X, Y)) ≫
      p.ν.hom.app ((S₀).tensor.obj (X, Y)) at hi'
  let a := (GD).mapIso (iTensor.app (X, Y)) ≪≫ M'.μ.app ((FD).obj X, (FD).obj Y)
  let b := (ID).mapIso (M.μ.app (X, Y)) ≪≫ sTensor.app ((HD).obj X, (HD).obj Y)
  have hInv : (S₃).tensor.map (Prod.mkHom (p.ν.hom.app X) (p.ν.hom.app Y)) ≫ b.inv =
      a.inv ≫ p.ν.hom.app ((S₀).tensor.obj (X, Y)) := by
    simpa only [a, b, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using hi'
  have hForward : a.hom ≫ (S₃).tensor.map (Prod.mkHom (p.ν.hom.app X) (p.ν.hom.app Y)) =
      p.ν.hom.app ((S₀).tensor.obj (X, Y)) ≫ b.hom := by
    apply (Iso.comp_inv_eq b).1
    rw [Category.assoc, hInv, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans hForward

end ReductionSquare

set_option maxHeartbeats 2000000 in
-- Assemble the normalized comparisons in four independent endpoint categories.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Any normalized geometric reduction square is monoidal for the prescribed normalized
endpoint tensor models. This statement constructs no geometric inverse image.
Source: Stacks 07A4, 0D6D; geometric-tensor-square proof step 3.
(blueprint: lem-sp-reduction-pullback-model-coherence).

Proof: construct the canonical ringed-site ordinary tensor comparisons and transport
away the identity scalar extension. Their canonical associator and unit equations make
these comparisons strong monoidal, with the required pure-section normalization.
The normalized exact derived monoidal construction gives coherent comparisons for the
native localization tensors. Transport them through the normalized comparisons between
the native tensors and the prescribed endpoint models. This produces both tensor models,
the two strong monoidal structures, and their representative equations.

The ordinary reduction square agrees on pulled coefficient-one pure tensors. Equality
on those generators is detected by the normalized module adjunction and the scalar and
sheaf tensor universal properties. Check its cochain extension on each signed bidegree
summand. On flat-term K-flat inputs, normalize both composite inverse tensorators using
the tower counits. The ordinary comparison identifies their image complexes, and hence
transports K-flatness between them. Apply the given square normalization at the two
inputs and their total tensor, and use naturality of the endpoint tensor model to compare
the two normalized composites. Two-variable localization extends this equality to all
derived objects. Finally the monoidal-square unit theorem determines the unit equation
from the tensor equation and the four strong monoidal structures. -/
theorem sp_reduction_pullback_model_coherence
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (M : SpReductionMonoidalTower l E T D r)
    {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (M' : SpReductionMonoidalTower l E T' D' r')
    (p : SpReductionPullbackTower l E T D r g D' r') :
    Nonempty (SpReductionPullbackCoherence l E T D r M g D' r' M' p) := by
  classical
  letI : PreservesFiniteLimits
      ((Scheme.proEtaleBaseChange g).op.lan :
        (T.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ T'.ProEtᵒᵖ ⥤ Type (u + 1)) := by
    letI : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    letI := flat_of_preservesFiniteLimits (Scheme.proEtaleBaseChange g)
    apply preservesFiniteLimits_op_lan_of_flat
  letI : PreservesFiniteLimits (Scheme.proEtaleSheafInverseImage g (Type (u + 1))) := by
    unfold Scheme.proEtaleSheafInverseImage Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  obtain ⟨iTensor, iModel, iCore, iPure, iTensor_eq, iFull⟩ :=
    inverseMonoidalModel.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T')
    (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction g (Type (u + 1))) p.integral
    M.source M'.source M.sourceModel M'.sourceModel
    M.sourceSymmetry M.sourceCoherence M'.sourceSymmetry M'.sourceCoherence
  obtain ⟨hc, ⟨adj⟩, hlim⟩ := spMonoidalSequenceInverseImage_leftExact g
  letI := hlim
  obtain ⟨sTensor, sModel, sCore, sPure, sTensor_eq, sFull⟩ :=
    inverseMonoidalModel.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T')
    (spMonoidalSequenceInverseImage T g) _ adj p.system
    M.target M'.target M.targetModel M'.targetModel
    M.targetSymmetry M.targetCoherence M'.targetSymmetry M'.targetCoherence
  have hTensor := reductionTensorSquare l E T D r M g D' r' M' p
    iTensor sTensor iModel sModel iPure sPure iFull sFull
  refine ⟨{ integralTensor := iTensor, integralModel := iModel, integralPure := iPure
            integralMonoidal := iCore, integral_tensor := iTensor_eq
            systemTensor := sTensor, systemModel := sModel, systemPure := sPure
            systemMonoidal := sCore, system_tensor := sTensor_eq
            tensor := hTensor, unit := ?_ }⟩
  let si : CoefFiniteHomStrong M.source M'.source
      p.integral.modules.mapDerivedCategory iTensor :=
    ⟨iCore, fun X Y ↦ Iso.ext (iTensor_eq X Y)⟩
  let ss : CoefFiniteHomStrong M.target M'.target
      p.system.modules.mapDerivedCategory sTensor :=
    ⟨sCore, fun X Y ↦ Iso.ext (sTensor_eq X Y)⟩
  let sm : CoefFiniteHomStrong M.source M.target
      (spMonoidalReduction l E T D r) M.μ :=
    ⟨M.monoidal, fun X Y ↦ Iso.ext (M.monoidal_tensor X Y)⟩
  let sm' : CoefFiniteHomStrong M'.source M'.target
      (spMonoidalReduction l E T' D' r') M'.μ :=
    ⟨M'.monoidal, fun X Y ↦ Iso.ext (M'.monoidal_tensor X Y)⟩
  have hu := coefficientMonoidalSquareUnit M.source M'.source M.target M'.target
    p.integral.modules.mapDerivedCategory p.system.modules.mapDerivedCategory
    (spMonoidalReduction l E T D r) (spMonoidalReduction l E T' D' r')
    iTensor sTensor M.μ M'.μ p.ν si ss sm sm' (fun X Y ↦ (hTensor X Y).symm)
  let ei := @Functor.CoreMonoidal.εIso _ _ M.source.monoidal _ _ M'.source.monoidal
    p.integral.modules.mapDerivedCategory iCore
  let es := @Functor.CoreMonoidal.εIso _ _ M.target.monoidal _ _ M'.target.monoidal
    p.system.modules.mapDerivedCategory sCore
  let em := @Functor.CoreMonoidal.εIso _ _ M.source.monoidal _ _ M.target.monoidal
    (spMonoidalReduction l E T D r) M.monoidal
  let em' := @Functor.CoreMonoidal.εIso _ _ M'.source.monoidal _ _ M'.target.monoidal
    (spMonoidalReduction l E T' D' r') M'.monoidal
  let a := em' ≪≫ (spMonoidalReduction l E T' D' r').mapIso ei
  let b := es ≪≫ p.system.modules.mapDerivedCategory.mapIso em
  change p.ν.hom.app M.source.monoidal.tensorUnit ≫ b.inv = a.inv at hu
  have he : a.hom ≫ p.ν.hom.app M.source.monoidal.tensorUnit = b.hom := by
    apply (cancel_mono b.inv).1
    rw [Category.assoc, hu, Iso.hom_inv_id, Iso.hom_inv_id]
  simpa only [a, b, ei, es, em, em', Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] using he

end AlgebraicGeometry.ProEtale
