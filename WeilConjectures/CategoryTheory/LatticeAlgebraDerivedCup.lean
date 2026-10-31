/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.DiscreteLatticeKoszulResolution
public import WeilConjectures.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.CategoryTheory.Action.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.LatticeDerivedInvariantsTensor

public import WeilConjectures.CategoryTheory.LatticeAlgebraCochainMultiplication

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

attribute [local irreducible] Functor.mapDerivedCategory

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
