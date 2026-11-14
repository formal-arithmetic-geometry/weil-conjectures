/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Algebra.FiniteTorsionExtensionInduction
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing

/-!
# Prime-coefficient vanishing for a constant bounded torsion group

Source: Stacks Project, Tag 0F08, cyclic-coefficient step; Tag 0739, colimits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- A constant bounded torsion group has zero higher direct image if its relevant prime
cyclic coefficients do. A prime is irrelevant if multiplication by it is injective.

Source: Stacks Project, Tag 0F08, proof's cyclic-coefficient reduction; Tag 0739, cohomology and
filtered colimits; Mathlib.GroupTheory.FiniteAbelian.Basic. -/
theorem isZero_higherDirectImage_constant_of_prime_vanishing
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (n : ℕ) (hn : n ≠ 0) (hM : ∀ x : M, n • x = 0)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ n →
      ¬ Function.Injective (fun x : M ↦ r • x) →
      IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
          (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod r)))))) :
    IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj M)) := by
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  let G := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ q
  have hzero (A : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (hA : IsZero A) :
      IsZero ((C ⋙ G).obj A) := (C ⋙ G).map_isZero hA
  have hiso {A B : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)} (e : A ≅ B)
      (hA : IsZero ((C ⋙ G).obj A)) : IsZero ((C ⋙ G).obj B) :=
    hA.of_iso ((C ⋙ G).mapIso e).symm
  have hext (S : ShortComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
      (hS : S.ShortExact) (h₁ : IsZero ((C ⋙ G).obj S.X₁))
      (h₃ : IsZero ((C ⋙ G).obj S.X₃)) : IsZero ((C ⋙ G).obj S.X₂) := by
    have hSC : (S.map C).ShortExact := hS.map_of_exact C
    have hSG := hSC.map_exact_of_isHomological
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q) G rfl
    exact hSG.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  apply isZero_higherDirectImage_constant_of_finite_submodules h q M n hn hM
  intro N hN
  let : Finite N := hN
  apply ModuleCat.finite_torsion_property_of_prime
    (fun A ↦ IsZero ((C ⋙ G).obj A)) hzero (fun e hA ↦ hiso e hA) hext
    (ModuleCat.of (ULift.{u + 1} ℤ) N) n hn
  · intro x
    apply Subtype.ext
    exact hM x.val
  · intro r hr hrn hrN
    apply hprime r hr hrn
    intro hrM
    apply hrN
    intro x y hxy
    apply Subtype.ext
    apply hrM
    exact congrArg Subtype.val hxy

end AlgebraicGeometry.Etale
