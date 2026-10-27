/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.CategoryTheory.Action.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Sheaf.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor

/-! # Degree-zero cochain multiplication for lattice algebras

The signed cochain tensor and its unique multiplication on an equivariant algebra
concentrated in degree zero. The generic construction is proved by coproduct descent.
Source: the canonical lattice cup construction, paragraph (3), proof step 13
(blueprint: def-sfb-lattice-algebra-cochain-multiplication).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Profinite.DiscreteLattice
namespace DerivedCup

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)

/-- The raw cochain tensor coproducts exist in the small action category.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance actionCochainTensor (P Q : CochainComplex (Equivariant R r) ℤ) :
    HomologicalComplex.HasTensor P Q := fun _ ↦ inferInstance

/-- The raw cochain tensor coproducts exist in the original module category.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance moduleCochainTensor (P Q : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasTensor P Q := fun _ ↦ inferInstance

/-- Closed tensor preserves the empty colimit in the fixed small universe.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleTensorLeftEmpty (P : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R)) (tensorLeft P) := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    (Adjunction.ofIsLeftAdjoint (tensorLeft P)).leftAdjoint_preservesColimits
  exact h.preservesColimitsOfShape.preservesColimit

/-- Closed tensor preserves the empty colimit in the fixed small universe.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleTensorRightEmpty (P : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R)) (tensorRight P) := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
    (Adjunction.ofIsLeftAdjoint (tensorRight P)).leftAdjoint_preservesColimits
  exact h.preservesColimitsOfShape.preservesColimit

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleComplexMonoidal :
    MonoidalCategory (CochainComplex (Modules R) ℤ) :=
  HomologicalComplex.monoidalCategory (Modules R) (.up ℤ)

/-- The signed cochain tensor projection is the existing canonical one.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleComplexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (Modules R) ℤ) :=
  (moduleComplexMonoidal R).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory (Modules R) (.up ℤ)) :=
  HomotopyCategory.MonoidalCategory.instMonoidalCategory (Modules R) (.up ℤ)

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleDerivedMonoidal :
    MonoidalCategory (DerivedCategory.{u + 2} (Modules R)) :=
  DerivedCategory.instMonoidalCategory_weilConjectures (Modules R)

/-- The derived tensor projection is the existing K-flat tensor projection.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleDerivedMonoidalStruct :
    MonoidalCategoryStruct (DerivedCategory.{u + 2} (Modules R)) :=
  (moduleDerivedMonoidal R).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) moduleLocalizationLax :
    (DerivedCategory.Q.{u + 2} (C := Modules R)).LaxMonoidal :=
  DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures (Modules R)

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) actionComplexMonoidal :
    MonoidalCategory (CochainComplex (Equivariant R r) ℤ) :=
  HomologicalComplex.monoidalCategory (Equivariant R r) (.up ℤ)

/-- The signed cochain tensor projection is the existing canonical one.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) actionComplexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (Equivariant R r) ℤ) :=
  (actionComplexMonoidal R r).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) actionHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory (Equivariant R r) (.up ℤ)) :=
  HomotopyCategory.MonoidalCategory.instMonoidalCategory (Equivariant R r) (.up ℤ)

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) actionDerivedMonoidal :
    MonoidalCategory (DerivedCategory.{u + 2} (Equivariant R r)) :=
  DerivedCategory.instMonoidalCategory_weilConjectures (Equivariant R r)

/-- The derived tensor projection is the existing K-flat tensor projection.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) actionDerivedMonoidalStruct :
    MonoidalCategoryStruct (DerivedCategory.{u + 2} (Equivariant R r)) :=
  (actionDerivedMonoidal R r).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
instance (priority := 1200) actionLocalizationLax :
    (DerivedCategory.Q.{u + 2} (C := Equivariant R r)).LaxMonoidal :=
  DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures (Equivariant R r)

attribute [local irreducible] Functor.mapDerivedCategory

/-- An algebra with lattice automorphisms is a monoid object in diagonal action modules.
Commutativity is the existing `IsCommMonObj` predicate, imposed in the main theorem.
Source: paragraph (3) (blueprint: def-sfb-lattice-algebra-cochain-multiplication). -/
abbrev Algebra := Mon (Equivariant R r)

/-- The selected cochain tensor is the actual signed total tensor construction.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication).
Proof: the monoidal structure on cochain complexes is induced from graded objects and
its object tensor is defined to be `HomologicalComplex.tensorObj`; unfolding gives reflexivity. -/
theorem cochainTensor_eq (P Q : CochainComplex (Equivariant R r) ℤ) :
    HomologicalComplex.tensorObj P Q = P ⊗ Q := by
  rfl

private theorem singleTensorMultiplicationExists
    {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [HasZeroObject C] (X : C) (μ : X ⊗ X ⟶ X)
    [HomologicalComplex.HasTensor
      ((HomologicalComplex.single C (.up ℤ) 0).obj X)
      ((HomologicalComplex.single C (.up ℤ) 0).obj X)] :
    ∃! m : HomologicalComplex.tensorObj
        ((HomologicalComplex.single C (.up ℤ) 0).obj X)
        ((HomologicalComplex.single C (.up ℤ) 0).obj X) ⟶
        (HomologicalComplex.single C (.up ℤ) 0).obj X,
      (MonoidalCategoryStruct.tensorHom (C := C)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv) ≫
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single C (.up ℤ) 0).obj X)
        ((HomologicalComplex.single C (.up ℤ) 0).obj X) 0 0 0 rfl ≫ m.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom =
        μ := by
  let S := (HomologicalComplex.single C (.up ℤ) 0).obj X
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  have hz (p q : ℤ) (h : p ≠ 0 ∨ q ≠ 0) : IsZero (S.X p ⊗ S.X q) := by
    rcases h with hp | hq
    · exact (tensorRight (S.X q)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X p hp)
    · exact (tensorLeft (S.X p)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X q hq)
  have ht (n : ℤ) (hn : n ≠ 0) : IsZero ((HomologicalComplex.tensorObj S S).X n) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply (hz p q (by
      change p + q = n at hpq
      omega)).eq_of_src
  let f : ∀ (p q : ℤ), p + q = 0 → (S.X p ⊗ S.X q ⟶ X) := fun p q hpq ↦ by
    by_cases hp : p = 0
    · subst p
      have hq : q = 0 := by omega
      subst q
      exact (e.hom ⊗ₘ e.hom) ≫ μ
    · exact 0
  let φ : (HomologicalComplex.tensorObj S S).X 0 ⟶ X :=
    HomologicalComplex.mapBifunctorDesc (K₁ := S) (K₂ := S)
      (F := curriedTensor C) (c := .up ℤ) f
  have hφ : HomologicalComplex.ιTensorObj S S 0 0 0 rfl ≫ φ =
      (e.hom ⊗ₘ e.hom) ≫ μ := by
    exact HomologicalComplex.ι_mapBifunctorDesc (K₁ := S) (K₂ := S)
        (F := curriedTensor C) (c := .up ℤ) f 0 0 rfl
  have hc (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
      (HomologicalComplex.tensorObj S S).d i 0 ≫ φ = 0 := by
    apply (ht i (by change i + 1 = 0 at hi; omega)).eq_of_src
  let m : HomologicalComplex.tensorObj S S ⟶ S := HomologicalComplex.mkHomToSingle φ hc
  have hm : (e.inv ⊗ₘ e.inv) ≫ HomologicalComplex.ιTensorObj S S 0 0 0 rfl ≫
      m.f 0 ≫ e.hom = μ := by
    change (e.inv ⊗ₘ e.inv) ≫ HomologicalComplex.ιTensorObj S S 0 0 0 rfl ≫
      (HomologicalComplex.mkHomToSingle φ hc).f 0 ≫ e.hom = _
    rw [HomologicalComplex.mkHomToSingle_f]
    simp only [Category.assoc]
    change (e.inv ⊗ₘ e.inv) ≫ HomologicalComplex.ιTensorObj S S 0 0 0 rfl ≫
      φ ≫ e.inv ≫ e.hom = _
    rw [Iso.inv_hom_id, Category.comp_id, hφ, ← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Iso.inv_hom_id, id_tensorHom_id, Category.id_comp]
  refine ⟨m, hm, ?_⟩
  intro m' hm'
  apply HomologicalComplex.to_single_hom_ext
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = 0 := by change 0 + q = 0 at hpq; omega
    subst q
    have heq := hm'.trans hm.symm
    apply (cancel_epi (e.inv ⊗ₘ e.inv)).1
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc] using heq
  · exact (hz p q (Or.inl hp)).eq_of_src _ _


/-- Multiplication on the raw degree-zero total tensor is uniquely determined by B.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-cochain-multiplication).
Proof: the two single complexes vanish outside zero, so their raw total tensor is
concentrated in zero. The displayed pure-tensor equation fixes its only component;
zero differentials give a chain map and the same coordinates prove uniqueness. -/
theorem singleMultiplicationExists (B : Algebra R r) :
    ∃! m : HomologicalComplex.tensorObj
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X)
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X) ⟶
        (HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X,
      (MonoidalCategoryStruct.tensorHom (C := Equivariant R r)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).inv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).inv) ≫
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X)
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X) 0 0 0 rfl ≫ m.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom =
        MonObj.mul (X := B.X) := by
  exact singleTensorMultiplicationExists B.X (MonObj.mul (X := B.X))

end DerivedCup
end Profinite.DiscreteLattice
