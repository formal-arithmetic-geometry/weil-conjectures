/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.Nat.Choose.Basic

/-! # Affine support from successive cones

Source: Stacks Project, Tag 08EK (Lemma 36.13.10), proof, cone construction
(blueprint: lem-sc-affine-support-iterated-cones).
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
`F` with binomial multiplicities. Global functions are encoded as compatible families of
local sections and act by `schemeDerivedScalar`; `g' i` is the restriction of `g i` to `U`
(tied by its value on the top open). Restriction to `U` is the localized-site restriction
followed by `Scheme.Modules.overEquiv U`.
Source: Stacks Project, Tag 08EK (blueprint: lem-sc-affine-support-iterated-cones).

Proof:
1. Starting with the perfect object `C 0`, apply perfect two-out-of-three
   (`lem-pc-perfect-two-out-of-three`) to each distinguished cone triangle.
2. On `D(g i)`, the function `g i` is a unit. Its multiplication map is an
   isomorphism, so its cone is zero (Stacks, Tag 05QR). Later cones are also zero
   there, since they are cones of endomorphisms of zero. The union of these principal
   opens is the complement of the common zero set, giving cohomology vanishing.
3. On `U`, multiplication commutes with isomorphisms, shifts, and finite sums.
   Inductively the restriction at step `i` is a sum of shifts of `F`, so every
   generator acts by zero. A cone of zero on `K` is `K ⊕ K[1]`: take the sum of
   the rotated identity triangles (Stacks, Tags 05QR and 05QS) and use uniqueness
   of cones. Beginning with `F ⊕ F[1]`, Pascal's identity gives multiplicity
   `Nat.choose (s + 1) j` after `s` cones. -/
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
  sorry

end AlgebraicGeometry.Scheme
