/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.Nat.Choose.Basic
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.ScalarConeStalkVanishing
import WeilConjectures.AlgebraicGeometry.RestrictedScalarConeSplit
import WeilConjectures.AlgebraicGeometry.BinomialShiftBiproduct

/-! # Affine support from successive cones

## References

* Stacks Project, Tag 08EK
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Successive cones of multiplication by the functions `g` are perfect and supported on
their common zero set. If the initial restriction to a quasi-compact open `U` is `F ⊕ F[1]`
and every function acts by zero on `F`, the final restriction is the sum of the shifts of
`F` with binomial multiplicities (Stacks, Tag 08EK). -/
theorem affine_support_iterated_cones (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    (s : ℕ) (g : Fin s → RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (C : Fin (s + 1) → schemeDerivedCategory X)
    (hE : IsPerfect X (C 0))
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (b : ∀ i : Fin s, C i.castSucc ⟶ C i.succ)
    (d : ∀ i : Fin s, C i.succ ⟶ (C i.castSucc)⟦(1 : ℤ)⟧)
    (hcone : ∀ i : Fin s,
      Triangle.mk (schemeDerivedScalar X (g i) (𝟙 (C i.castSucc))) (b i) (d i) ∈
        distTriang (schemeDerivedCategory X)) :
    IsPerfect X (C (Fin.last s)) ∧
    (∀ (n : ℤ) (x : X), (∃ i : Fin s, x ∈ X.basicOpen ((g i).val (op ⊤))) →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
          (C (Fin.last s))).val.presheaf x))) ∧
    (IsCompact (U : Set X) →
    ∀ F : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme F →
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj (C 0) ≅ F ⊞ F⟦(1 : ℤ)⟧) →
      ∀ (g' : Fin s →
          RingCat.sectionsSubring (U.toScheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})),
      (∀ i : Fin s, (g' i).val (op ⊤) = U.ι.appTop.hom ((g i).val (op ⊤))) →
      (∀ i : Fin s, schemeDerivedScalar U.toScheme (g' i) (𝟙 F) = 0) →
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj (C (Fin.last s)) ≅
          biproduct (fun p : (j : Fin (s + 2)) × Fin (Nat.choose (s + 1) j.val) ↦
            F⟦(p.1.val : ℤ)⟧))) := by
  have hperfect : ∀ i : Fin (s + 1), IsPerfect X (C i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact hE
    | succ i ih =>
      exact (isPerfect_two_out_of_three X _ (hcone i)).1 ih ih
  refine ⟨hperfect (Fin.last s), ?_, ?_⟩
  · have hsupport : ∀ k : Fin (s + 1), ∀ x : X,
        (∃ i : Fin s, i.val < k.val ∧ x ∈ X.basicOpen ((g i).val (op ⊤))) →
        ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj (C k)).val.presheaf x)) := by
      intro k
      induction k using Fin.induction with
      | zero =>
        intro x hx
        obtain ⟨i, hi, _⟩ := hx
        simp at hi
      | succ k ih =>
        intro x hx
        obtain ⟨i, hi, hx⟩ := hx
        apply scalar_cone_stalk_vanishing X (g k) (C k.castSucc) (C k.succ)
          (b k) (d k) (hcone k) x
        by_cases hik : i = k
        · subst i
          exact Or.inl hx
        · exact Or.inr (ih x ⟨i, by
            have : i.val ≠ k.val := fun h ↦ hik (Fin.ext h)
            simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢
            omega, hx⟩)
    intro n x hx
    obtain ⟨i, hi⟩ := hx
    exact hsupport (Fin.last s) x ⟨i, i.isLt, hi⟩ n
  · intro _ F _ hF g' hg hzero
    let R := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    have hsplit : ∀ k : Fin (s + 1), Nonempty
        (R.obj (C k) ≅ biproduct
          (fun p : (j : Fin (k.val + 2)) × Fin (Nat.choose (k.val + 1) j.val) ↦
            F⟦(p.1.val : ℤ)⟧)) := by
      intro k
      induction k using Fin.induction with
      | zero =>
        obtain ⟨e⟩ := hF
        obtain ⟨e₀⟩ := (binomial_shift_biproduct U.toScheme F).1
        exact ⟨e ≪≫ e₀⟩
      | succ k ih =>
        obtain ⟨e⟩ := ih
        obtain ⟨econe⟩ := restricted_scalar_cone_split X U (g k) (g' k) (hg k)
          (C k.castSucc) (C k.succ) (b k) (d k) (hcone k) F (hzero k)
          ((j : Fin (k.val + 2)) × Fin (Nat.choose (k.val + 1) j.val))
          (fun p ↦ (p.1.val : ℤ)) ⟨e⟩
        obtain ⟨epascal⟩ := (binomial_shift_biproduct U.toScheme F).2 (k.val + 1)
        exact ⟨econe ≪≫ biprod.mapIso e ((shiftFunctor _ (1 : ℤ)).mapIso e) ≪≫ epascal⟩
    exact hsplit (Fin.last s)

end AlgebraicGeometry.Scheme
