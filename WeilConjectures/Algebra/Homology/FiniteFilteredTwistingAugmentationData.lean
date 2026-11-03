/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
public import WeilConjectures.CategoryTheory.UniformFiniteFilteredLocalization

/-! # Augmentations of finite twisting families

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, the successive
mapping-cylinder construction of filtered flat resolutions.
(blueprint: def-trf-finite-filtered-twisting-augmentation-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

/-- The component equations for an augmentation of a finite twisting family.
The components land in the actual filtration steps. They need not be chain maps;
their defects are exactly the strictly higher twisting terms. The maps to the grades
are genuine chain maps, specified by the canonical quotient projections.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, mapping cylinders
(blueprint: def-trf-finite-filtered-twisting-augmentation-data). -/
structure FiniteFilteredTwistingAugmentation (D : FiniteTwistingFamily R a b)
    (M : FilteredObject (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)) where
  component : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    (D.G p).X n ⟶ (M.filtration.F p.val : CochainComplex _ ℤ).X n
  comm : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    component p n ≫ (Subobject.underlying.obj (M.filtration.F p.val)).d n (n + 1) =
      (D.G p).d n (n + 1) ≫ component p (n + 1) +
        ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
          D.τ p q.val q.property n ≫ component q.val (n + 1) ≫
            (Subobject.ofLE (M.filtration.F q.val.val) (M.filtration.F p.val)
              (M.filtration.antitone (le_of_lt q.property))).f (n + 1)
  grade : ∀ p : ↥(Finset.Icc a b), D.G p ⟶ M.filtration.gradedPiece p.val
  grade_f : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    (grade p).f n = component p n ≫
      (M.filtration.complexQuotientπ p.val (p.val + 1) (by omega)).f n

end CochainComplex
