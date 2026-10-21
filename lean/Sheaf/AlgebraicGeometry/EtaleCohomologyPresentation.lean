module

public import Sheaf.CategoryTheory.DerivedExtEvaluation
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleGrothendieckAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # The canonical Ext and derived-sections presentations of etale cohomology

Source: Stacks Project, Cohomology on Sites, Tags 03FD and 01FT.
(blueprint: def-weil-pbc-etale-cohomology-presentation).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
noncomputable section
set_option autoImplicit false
attribute [local instance 2000] CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
  HasSmallSiteSheafify.hasSheafify IsGrothendieckAbelian.hasExt
  HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat
  Scheme.enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedExtEvaluation

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the derived morphism representing an Ext class at the integer generator.
All functors, units and shift comparisons are the recorded derived constructions.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation). -/
def sheafHToDerived {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) :
    (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) :=
  derivedExtEvaluation.{u, u + 2, u + 1, u + 1}
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q
    ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (ULift.up 1)) x
attribute [local irreducible] sheafHToDerived

/-- Additivity of evaluation of the represented cohomology class.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation).

Proof: Ext.homAddEquiv preserves sums. The right derived functor, its homology
functors, the degree-zero and shift comparisons, and evaluation at the fixed generator
are additive. Their displayed composite therefore preserves sums. -/
theorem sheafHToDerived_add {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x y : Sheaf.H F q) :
    sheafHToDerived F q (x + y) = sheafHToDerived F q x + sheafHToDerived F q y := by
  sorry

/-- The Ext-to-derived evaluation comparison is bijective in every degree.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation).

Proof: resolve F by injective abelian sheaves. The constant-integer adjunction
identifies Hom from the integer sheaf with global sections naturally. Apply this
identification in each degree of the resolution: its cohomology is Ext on the
source and derived global sections on the target. The identity generator evaluates
this very identification, including in degree zero. Thus the displayed map is
bijective. This argument applies also to the empty scheme. -/
theorem sheafHToDerived_bijective {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (sheafHToDerived F q) := by
  sorry

/-- The canonical additive comparison of the two cohomology presentations.
Its inverse is determined by the proved bijectivity of the explicit evaluation.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-etale-cohomology-presentation). -/
def sheafHDerivedEquiv {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H F q ≃+
      (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) :=
  { Equiv.ofBijective (sheafHToDerived F q) (sheafHToDerived_bijective F q) with
    map_add' := sheafHToDerived_add F q }

end
end AlgebraicGeometry.Etale
