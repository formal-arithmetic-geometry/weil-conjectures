/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarColimits

import WeilConjectures.CategoryTheory.CanonicalDerivedLax.CanonicalTensorDerived

/-! # Canonical tensor data for component evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
private def pair (M N : PointMod ℓ k)
    (x : (pointSections ℓ k).obj M) (y : (pointSections ℓ k).obj N) :
    (pointSections ℓ k).obj (M ⊗ N) := (λ_ (𝟙_ (PointMod ℓ k))).inv ≫ (x ⊗ₘ y)
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve scalar actions through the point-section and sheaf tensor module instances.
private lemma pair_smul_left (M N : PointMod ℓ k)
    (a : ULift.{u + 1} (PadicAlgCl ℓ))
    (x : (pointSections ℓ k).obj M) (y : (pointSections ℓ k).obj N) :
    pair ℓ k M N (a • x) y = (a • pair ℓ k M N x y : (pointSections ℓ k).obj (M ⊗ N)) := by
  change (λ_ (𝟙_ (PointMod ℓ k))).inv ≫
      ((pointUnitEndRingHom ℓ k a.down ≫ x) ⊗ₘ y) =
    pointUnitEndRingHom ℓ k a.down ≫ (λ_ (𝟙_ (PointMod ℓ k))).inv ≫ (x ⊗ₘ y)
  change (𝟙_ (PointMod ℓ k) ⟶ M) at x
  change (𝟙_ (PointMod ℓ k) ⟶ N) at y
  have h : ((pointUnitEndRingHom ℓ k a.down) ⊗ₘ 𝟙 _) ≫ (x ⊗ₘ y) =
      ((pointUnitEndRingHom ℓ k a.down ≫ x) ⊗ₘ y) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [← h, unitors_inv_equal, tensorHom_id,
    ← rightUnitor_inv_naturality_assoc]
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve scalar actions through the point-section and sheaf tensor module instances.
private lemma pair_smul_right (M N : PointMod ℓ k)
    (a : ULift.{u + 1} (PadicAlgCl ℓ))
    (x : (pointSections ℓ k).obj M) (y : (pointSections ℓ k).obj N) :
    pair ℓ k M N x (a • y) = (a • pair ℓ k M N x y : (pointSections ℓ k).obj (M ⊗ N)) := by
  change (λ_ (𝟙_ (PointMod ℓ k))).inv ≫
      (x ⊗ₘ (pointUnitEndRingHom ℓ k a.down ≫ y)) =
    pointUnitEndRingHom ℓ k a.down ≫ (λ_ (𝟙_ (PointMod ℓ k))).inv ≫ (x ⊗ₘ y)
  change (𝟙_ (PointMod ℓ k) ⟶ M) at x
  change (𝟙_ (PointMod ℓ k) ⟶ N) at y
  have h : (𝟙 _ ⊗ₘ (pointUnitEndRingHom ℓ k a.down)) ≫ (x ⊗ₘ y) =
      (x ⊗ₘ (pointUnitEndRingHom ℓ k a.down ≫ y)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [← h, id_tensorHom, ← leftUnitor_inv_naturality_assoc]
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve scalar actions through the point-section and sheaf tensor module instances.
set_option maxHeartbeats 800000 in
-- The bilinear map contains several nested scalar-action instance searches.
private def pairing (M N : PointMod ℓ k) :
    (pointSections ℓ k).obj M →ₗ[ULift.{u + 1} (PadicAlgCl ℓ)]
      (pointSections ℓ k).obj N →ₗ[ULift.{u + 1} (PadicAlgCl ℓ)]
        (pointSections ℓ k).obj (M ⊗ N) where
  toFun x :=
    { toFun := pair ℓ k M N x
      map_add' := by
        intro y z
        change (𝟙_ (PointMod ℓ k) ⟶ M) at x
        change (𝟙_ (PointMod ℓ k) ⟶ N) at y z
        change (λ_ (𝟙_ (PointMod ℓ k))).inv ≫ (x ⊗ₘ (y + z)) = _
        rw [MonoidalPreadditive.tensor_add, Preadditive.comp_add]
        rfl
      map_smul' := fun a y => pair_smul_right ℓ k M N a x y }
  map_add' := by
    intro x y
    ext z
    change (𝟙_ (PointMod ℓ k) ⟶ M) at x y
    change (𝟙_ (PointMod ℓ k) ⟶ N) at z
    change (λ_ (𝟙_ (PointMod ℓ k))).inv ≫ ((x + y) ⊗ₘ z) = _
    rw [MonoidalPreadditive.add_tensor, Preadditive.comp_add]
    rfl
  map_smul' := by intros; ext; exact pair_smul_left ℓ k M N _ _ _
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve scalar actions through the point-section and sheaf tensor module instances.
private def tensorMap (M N : PointMod ℓ k) :
    (pointSections ℓ k).obj M ⊗ (pointSections ℓ k).obj N ⟶
      (pointSections ℓ k).obj (M ⊗ N) :=
  ModuleCat.homEquiv.symm
    (TensorProduct.lift (pairing ℓ k M N))
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve scalar actions through the point-section and sheaf tensor module instances.
private lemma tensorMap_apply (M N : PointMod ℓ k)
    (x : (pointSections ℓ k).obj M) (y : (pointSections ℓ k).obj N) :
    (tensorMap ℓ k M N).hom (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl ℓ)] y) =
      pair ℓ k M N x y := rfl
private lemma pair_natural {M M' N N' : PointMod ℓ k}
    (f : M ⟶ M') (g : N ⟶ N')
    (x : (pointSections ℓ k).obj M) (y : (pointSections ℓ k).obj N) :
    pair ℓ k M' N' (x ≫ f) (y ≫ g) = pair ℓ k M N x y ≫ (f ⊗ₘ g) := by
  simp only [pair, tensorHom_comp_tensorHom, Category.assoc]
private lemma pair_assoc (M N P : PointMod ℓ k)
    (x : (pointSections ℓ k).obj M) (y : (pointSections ℓ k).obj N)
    (z : (pointSections ℓ k).obj P) :
    pair ℓ k (M ⊗ N) P (pair ℓ k M N x y) z ≫ (α_ M N P).hom =
      pair ℓ k M (N ⊗ P) x (pair ℓ k N P y z) := by
  change (𝟙_ (PointMod ℓ k) ⟶ M) at x
  change (𝟙_ (PointMod ℓ k) ⟶ N) at y
  change (𝟙_ (PointMod ℓ k) ⟶ P) at z
  dsimp only [pair]
  have h : (λ_ (𝟙_ (PointMod ℓ k))).inv ≫
      ((λ_ (𝟙_ (PointMod ℓ k))).inv ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom =
    (λ_ (𝟙_ (PointMod ℓ k))).inv ≫
      (𝟙 _ ⊗ₘ (λ_ (𝟙_ (PointMod ℓ k))).inv) := by monoidal
  have h₁ : ((λ_ (𝟙_ (PointMod ℓ k))).inv ⊗ₘ 𝟙 _) ≫
      ((x ⊗ₘ y) ⊗ₘ z) = ((λ_ (𝟙_ _)).inv ≫ (x ⊗ₘ y)) ⊗ₘ z := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have h₂ : (𝟙 _ ⊗ₘ (λ_ (𝟙_ (PointMod ℓ k))).inv) ≫
      (x ⊗ₘ (y ⊗ₘ z)) = x ⊗ₘ ((λ_ (𝟙_ _)).inv ≫ (y ⊗ₘ z)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [← h₁]
  simp only [Category.assoc]
  rw [associator_naturality]
  rw [reassoc_of% h]
  rw [h₂]
private lemma pair_left_unit (M : PointMod ℓ k)
    (x : (pointSections ℓ k).obj M) :
    pair ℓ k (𝟙_ _) M (𝟙 _) x ≫ (λ_ M).hom = x := by
  dsimp only [pair]
  rw [Category.assoc, id_tensorHom, leftUnitor_naturality, Iso.inv_hom_id_assoc]
private lemma pair_right_unit (M : PointMod ℓ k)
    (x : (pointSections ℓ k).obj M) :
    pair ℓ k M (𝟙_ _) x (𝟙 _) ≫ (ρ_ M).hom = x := by
  dsimp only [pair]
  rw [Category.assoc, tensorHom_id, rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc]
variable [IsAlgClosed k]

private lemma pointUnitMap_apply (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    (pointSectionsUnitIso ℓ k).hom.hom a = a • pointSectionsUnit ℓ k := rfl
omit [IsAlgClosed k] in
private lemma pointMap_apply {M N : PointMod ℓ k} (f : M ⟶ N)
    (x : (pointSections ℓ k).obj M) :
    ((pointSections ℓ k).map f).hom x = x ≫ f := rfl
set_option maxHeartbeats 800000 in
-- Normalize the sheaf tensor and both scalar-module unit diagrams on pure tensors.
set_option synthInstance.maxHeartbeats 200000 in
-- The underlying point modules and scalar-restriction modules have deeply nested instances.
@[instance_reducible]
private def pointLax : (pointSections ℓ k).LaxMonoidal := by
  refine Functor.LaxMonoidal.ofTensorHom (pointSectionsUnitIso ℓ k).hom
    (tensorMap ℓ k) ?_ ?_ ?_ ?_
  · intro M M' N N' f g
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change pair ℓ k M' N' (x ≫ f) (y ≫ g) =
      pair ℓ k M N x y ≫ (f ⊗ₘ g)
    exact pair_natural ℓ k f g x y
  · intro M N P
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y z
    change pair ℓ k (M ⊗ N) P (pair ℓ k M N x y) z ≫ (α_ M N P).hom =
      pair ℓ k M (N ⊗ P) x (pair ℓ k N P y z)
    exact pair_assoc ℓ k M N P x y z
  · intro M
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.id_apply]
    erw [pointMap_apply, tensorMap_apply, pointUnitMap_apply, pair_smul_left]
    change pointUnitEndRingHom ℓ k a.down ≫ x =
      (pointUnitEndRingHom ℓ k a.down ≫
        pair ℓ k (𝟙_ _) M (pointSectionsUnit ℓ k) x) ≫ (λ_ M).hom
    rw [Category.assoc]
    exact congrArg (fun f ↦ pointUnitEndRingHom ℓ k a.down ≫ f)
      (pair_left_unit ℓ k M x).symm
  · intro M
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x a
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.id_apply]
    erw [pointMap_apply, tensorMap_apply, pointUnitMap_apply, pair_smul_right]
    change pointUnitEndRingHom ℓ k a.down ≫ x =
      (pointUnitEndRingHom ℓ k a.down ≫
        pair ℓ k M (𝟙_ _) x (pointSectionsUnit ℓ k)) ≫ (ρ_ M).hom
    rw [Category.assoc]
    exact congrArg (fun f ↦ pointUnitEndRingHom ℓ k a.down ≫ f)
      (pair_right_unit ℓ k M x).symm

variable (I : Type w) [Finite I]
@[instance_reducible]
private def sectionsLax (t : I) : (condensedBoundarySections ℓ k I t).LaxMonoidal := by
  let := pointLax ℓ k
  exact inferInstanceAs ((condensedBoundaryRestriction ℓ k I t ⋙
    pointSections ℓ k).LaxMonoidal)

private lemma sectionsLax_unit (t : I) :
    let := sectionsLax ℓ k I t
    (Functor.LaxMonoidal.ε (condensedBoundarySections ℓ k I t)).hom
      (1 : ULift.{u + 1} (PadicAlgCl ℓ)) =
        Functor.LaxMonoidal.ε (condensedBoundaryRestriction ℓ k I t) := by
  let := pointLax ℓ k
  change ((pointSections ℓ k).map
    (Functor.LaxMonoidal.ε (condensedBoundaryRestriction ℓ k I t))).hom
      ((pointSectionsUnitIso ℓ k).hom.hom 1) = _
  rw [pointUnitMap_apply, one_smul, pointMap_apply]
  change (𝟙 (𝟙_ (PointMod ℓ k))) ≫ _ = _
  exact Category.id_comp _

private lemma sectionsLax_tensor (t : I) (A B : CondensedBoundaryMod ℓ k I)
    (x : (condensedBoundarySections ℓ k I t).obj A)
    (y : (condensedBoundarySections ℓ k I t).obj B) :
    let := sectionsLax ℓ k I t
    (Functor.LaxMonoidal.μ (condensedBoundarySections ℓ k I t) A B).hom
      (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl ℓ)] y) =
    (λ_ (𝟙_ (PointMod ℓ k))).inv ≫ (x ⊗ₘ y) ≫
      Functor.LaxMonoidal.μ (condensedBoundaryRestriction ℓ k I t) A B := by
  let := pointLax ℓ k
  change ((pointSections ℓ k).map
    (Functor.LaxMonoidal.μ (condensedBoundaryRestriction ℓ k I t) A B)).hom
      ((tensorMap ℓ k _ _).hom (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl ℓ)] y)) = _
  rw [tensorMap_apply, pointMap_apply]
  exact Category.assoc _ _ _

private theorem sectionsLax_unit_isIso (t : I) :
    let := sectionsLax ℓ k I t
    IsIso (Functor.LaxMonoidal.ε (condensedBoundarySections ℓ k I t)) := by
  let := pointLax ℓ k
  change IsIso ((pointSectionsUnitIso ℓ k).hom ≫ (pointSections ℓ k).map
    (Functor.LaxMonoidal.ε (condensedBoundaryRestriction ℓ k I t)))
  infer_instance



set_option linter.unusedVariables false in
-- Retain the original statement's named instance binder, used implicitly by its predicate.
set_option maxHeartbeats 1200000 in
-- Normalize the exact-derived comparison and the native derived tensor instances.
/-- Existence of the normalized tensor data of component evaluation.
Source: blueprint local boundary duality, Step 5, evaluation and totalization formulas.
Take section tensor on pure tensors to the product of their scalar coordinates and section
unit to the constant coefficient unit. Restriction preserves the unit and tensor product.
Derive these maps by the total-complex summand formula, using the totalization inclusion
of each pair of degrees. The section formulas give the unit and associativity diagrams;
localization carries those identities to the derived category. Evaluation of the coefficient
unit identifies it with the scalar unit. These constructions give all five normalizations,
including for an empty boundary or a zero complex.
(blueprint: lem-a1-condensed-point-canonical-tensor) -/
theorem condensed_point_canonical_tensor [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    Exists fun [s : CondensedBoundaryEvaluationTensor ℓ k I] ↦
      IsCanonicalCondensedBoundaryEvaluationTensor ℓ k I := by
  let (t : I) : (condensedBoundarySections ℓ k I t).LaxMonoidal :=
    sectionsLax ℓ k I t
  choose m hu ht using fun t : I ↦
    CategoryTheory.CanonicalDerivedLax.exists_normalized (condensedBoundarySections ℓ k I t)
  have hε (t : I) : IsIso ((m t).ε) := by
    have := sectionsLax_unit_isIso ℓ k I t
    have : IsIso (Functor.LaxComplex.chainUnit (condensedBoundarySections ℓ k I t)) := by
      dsimp only [Functor.LaxComplex.chainUnit]
      infer_instance
    have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C :=
        ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))))) :=
      CategoryTheory.RingedDerivedNative.localization_isIso_ε
    have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C :=
        CondensedBoundaryMod ℓ k I))) :=
      CategoryTheory.RingedDerivedNative.localization_isIso_ε
    have : IsIso ((m t).ε ≫ (condensedBoundarySections ℓ k I t).mapDerivedCategory.map
        (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
          (condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.hom.app (𝟙_ _)) := by
      rw [hu t]
      infer_instance
    exact IsIso.of_isIso_comp_right (m t).ε
      ((condensedBoundarySections ℓ k I t).mapDerivedCategory.map
          (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := CondensedBoundaryMod ℓ k I))) ≫
        (condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.hom.app (𝟙_ _))
  let s : CondensedBoundaryEvaluationTensor ℓ k I :=
    { sections := sectionsLax ℓ k I
      fiber := m
      unit := fun t ↦ (asIso (m t).ε).symm }
  let := s
  refine ⟨s, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact sectionsLax_unit ℓ k I t
  · intro t A B x y
    exact sectionsLax_tensor ℓ k I t A B x y
  · intro t
    rfl
  · intro t
    exact hu t
  · intro t P Q
    refine ⟨Functor.LaxComplex.chainTensor (condensedBoundarySections ℓ k I t) P Q,
      fun p q ↦ Functor.LaxComplex.ιTensorObj_chainTensor_f _ P Q p q (p + q) rfl, ?_⟩
    have h := congrArg (fun f ↦
      ((condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.inv.app P ⊗ₘ
        (condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.inv.app Q) ≫ f)
      (ht t P Q)
    dsimp only [condensedBoundaryFiber]
    simpa only [← Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp] using h
end AlgebraicGeometry.ProEtale.CondensedRing
