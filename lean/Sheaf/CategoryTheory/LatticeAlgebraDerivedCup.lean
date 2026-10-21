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

/-! # Canonical derived cups for discrete-lattice equivariant algebras

Source: main-20261015 direct-image proof, paragraph (3), agent expansion
(blueprint: def-sfb-lattice-algebra-derived-cup).

## Main definitions

* `Algebra`: an internal unital algebra with lattice automorphisms.
* `algebraMultiply`: the localized original algebra multiplication.
* `cup`, `cupUnit`: tensor-of-counits cup and canonical derived unit.
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
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance actionCochainTensor (P Q : CochainComplex (Equivariant R r) ℤ) :
    HomologicalComplex.HasTensor P Q := fun _ ↦ inferInstance

/-- The raw cochain tensor coproducts exist in the original module category.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance moduleCochainTensor (P Q : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasTensor P Q := fun _ ↦ inferInstance

/-- Closed tensor preserves the empty colimit in the fixed small universe.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleTensorLeftEmpty (P : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R)) (tensorLeft P) := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    (Adjunction.ofIsLeftAdjoint (tensorLeft P)).leftAdjoint_preservesColimits
  exact h.preservesColimitsOfShape.preservesColimit

/-- Closed tensor preserves the empty colimit in the fixed small universe.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleTensorRightEmpty (P : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R)) (tensorRight P) := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
    (Adjunction.ofIsLeftAdjoint (tensorRight P)).leftAdjoint_preservesColimits
  exact h.preservesColimitsOfShape.preservesColimit

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleComplexMonoidal :
    MonoidalCategory (CochainComplex (Modules R) ℤ) :=
  HomologicalComplex.monoidalCategory (Modules R) (.up ℤ)

/-- The signed cochain tensor projection is the existing canonical one.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleComplexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (Modules R) ℤ) :=
  (moduleComplexMonoidal R).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory (Modules R) (.up ℤ)) :=
  HomotopyCategory.MonoidalCategory.instMonoidalCategory (Modules R) (.up ℤ)

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleDerivedMonoidal :
    MonoidalCategory (DerivedCategory.{u + 2} (Modules R)) :=
  DerivedCategory.instMonoidalCategory_weilConjectures (Modules R)

/-- The derived tensor projection is the existing K-flat tensor projection.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleDerivedMonoidalStruct :
    MonoidalCategoryStruct (DerivedCategory.{u + 2} (Modules R)) :=
  (moduleDerivedMonoidal R).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) moduleLocalizationLax :
    (DerivedCategory.Q.{u + 2} (C := Modules R)).LaxMonoidal :=
  DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures (Modules R)

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) actionComplexMonoidal :
    MonoidalCategory (CochainComplex (Equivariant R r) ℤ) :=
  HomologicalComplex.monoidalCategory (Equivariant R r) (.up ℤ)

/-- The signed cochain tensor projection is the existing canonical one.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) actionComplexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (Equivariant R r) ℤ) :=
  (actionComplexMonoidal R r).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) actionHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory (Equivariant R r) (.up ℤ)) :=
  HomotopyCategory.MonoidalCategory.instMonoidalCategory (Equivariant R r) (.up ℤ)

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) actionDerivedMonoidal :
    MonoidalCategory (DerivedCategory.{u + 2} (Equivariant R r)) :=
  DerivedCategory.instMonoidalCategory_weilConjectures (Equivariant R r)

/-- The derived tensor projection is the existing K-flat tensor projection.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) actionDerivedMonoidalStruct :
    MonoidalCategoryStruct (DerivedCategory.{u + 2} (Equivariant R r)) :=
  (actionDerivedMonoidal R r).toMonoidalCategoryStruct

/-- The existing canonical tensor structure, retained by name to avoid repeated synthesis.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
instance (priority := 1200) actionLocalizationLax :
    (DerivedCategory.Q.{u + 2} (C := Equivariant R r)).LaxMonoidal :=
  DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures (Equivariant R r)

attribute [local irreducible] Functor.mapDerivedCategory

/-- An algebra with lattice automorphisms is a monoid object in diagonal action modules.
Commutativity is the existing `IsCommMonObj` predicate, imposed in the main theorem.
Source: paragraph (3) (blueprint: def-sfb-lattice-algebra-derived-cup). -/
abbrev Algebra := Mon (Equivariant R r)

/-- The selected cochain tensor is the actual signed total tensor construction.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup).
Proof: the monoidal structure on cochain complexes is induced from graded objects and
its object tensor is defined to be `HomologicalComplex.tensorObj`; unfolding gives reflexivity. -/
theorem cochainTensor_eq (P Q : CochainComplex (Equivariant R r) ℤ) :
    HomologicalComplex.tensorObj P Q = P ⊗ Q := by
  sorry

/-- Multiplication on the raw degree-zero total tensor is uniquely determined by B.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup).
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
  sorry

/-- The unique multiplication with the original B-coordinate on the zero tensor summand.
Source: paragraph (3) (blueprint: def-sfb-lattice-algebra-derived-cup). -/
def singleMultiplication (B : Algebra R r) := (singleMultiplicationExists R r B).exists.choose

/-- The canonical ordinary algebra unit has trivial source action and underlying 1_B.
Source: paragraph (3) (blueprint: def-sfb-lattice-algebra-derived-cup). -/
def ordinaryAlgebraUnit (B : Algebra R r) : (trivial R r).obj (𝟙_ (Modules R)) ⟶ B.X :=
  MonObj.one (X := B.X)

/-- Mathlib's canonical identification between the two degree-zero derived presentations.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-algebra-derived-cup). -/
def singleQIso (B : Algebra R r) :=
  eqToIso (DerivedCategory.Q_obj_single_obj.{u + 2} (Equivariant R r) 0 B.X).symm

/-- Canonical derived multiplication induced by the equivariant multiplication of B.
Source: paragraph (3) (blueprint: def-sfb-lattice-algebra-derived-cup). -/
def algebraMultiply (B : Algebra R r) :
    (DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X ⊗
      (DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X ⟶
      (DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X :=
  ((singleQIso R r B).hom ⊗ₘ (singleQIso R r B).hom) ≫
    Functor.LaxMonoidal.μ (DerivedCategory.Q.{u + 2} (C := Equivariant R r))
      ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X)
      ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X) ≫
    DerivedCategory.Q.{u + 2}.map
      (eqToHom (cochainTensor_eq R r _ _).symm ≫ singleMultiplication R r B) ≫
        (singleQIso R r B).inv

/-- The canonical cup is the tensor-of-counits mate followed by multiplication of B.
It specializes at the regular trivial algebra to the unital cup of the restriction
calculus, since both use the invariant-inclusion adjunction and K-flat tensor comparison.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-algebra-derived-cup). -/
def cup (B : Algebra R r) :
    (derivedInvariants R r).obj
      ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X) ⊗
      (derivedInvariants R r).obj
      ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X) ⟶
      (derivedInvariants R r).obj
      ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X) :=
  Functor.LaxMonoidal.μ (derivedInvariants R r)
      ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X)
      ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X) ≫
    (derivedInvariants R r).map (algebraMultiply R r B)

/-- The canonical cup unit is the mate of the equivariant algebra unit.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-algebra-derived-cup). -/
def cupUnit (B : Algebra R r) :
    (DerivedCategory.singleFunctor.{u + 2} (Modules R) 0).obj (𝟙_ (Modules R)) ⟶
      (derivedInvariants R r).obj
        ((DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).obj B.X) :=
  (derivedAdjunction R r).unit.app _ ≫
    (derivedInvariants R r).map
      (((trivial R r).mapDerivedCategorySingleFunctor.{u + 2, u + 2} 0).hom.app
          (𝟙_ (Modules R)) ≫
        (DerivedCategory.singleFunctor.{u + 2} (Equivariant R r) 0).map
          (ordinaryAlgebraUnit R r B))

end DerivedCup
end Profinite.DiscreteLattice
