/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.OrbitTensorLineSections

/-! # Permutation linearizations of an orbit tensor

Source: Stacks Project, Tags 01CA and 01CD; the finite-permutation construction in
Step 2 of `lem-per-orbit-tensor-line-descent`.
(blueprint: lem-per-orbit-tensor-permutation-linearizations)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The finite orbit tensor has the permutation linearization and its tensor-power
linearizations. They obey the unit and cocycle laws and fix every orbit frame and
its pure powers, including degree zero. No quotient-ring or finiteness hypothesis
on q is needed for this construction, and L need not be invertible.

Source: Stacks Project, Modules, Tags 01CA and 01CD; Step 2 of the invariant-frame
argument for Rydh Proposition 4.7, written out in the parent node.
(blueprint: lem-per-orbit-tensor-permutation-linearizations)

Proof: distribute pullback over the finite iterated tensor using its unit-compatible
monoidal comparison. The composition comparisons identify the pulled-back factor
indexed by h with the factor indexed by hg. Right multiplication is a permutation
of the list enumerating H. Apply the symmetry and associativity maps to reorder
these factors. The symmetric monoidal coherence laws identify the identity
permutation with the normalized pullback identity, and the composite of the
permutations for g and h with that for gh; composition of the pullback comparisons
is coherent because they arise by uniqueness of normalized left adjoints.
Iterate the monoidal comparison for powers, taking the unit comparison at degree
zero. The section formulas for composition, tensor products and symmetry send
the tensor of the translates of s to the same tensor in its original order.
This proves both frame formulas for arbitrary s, without requiring s to generate.
The same coherence calculation proves the unit and cocycle formulas for powers. -/
theorem exists_orbit_tensor_linearizations {H : Type v} [Group H] [Finite H]
    {X Y : Scheme.{u}} (a : H → (X ≅ X))
    (a_one : (a 1).hom = 𝟙 X)
    (a_mul : ∀ g h : H, (a (g * h)).hom = (a h).hom ≫ (a g).hom)
    (q : X ⟶ Y) (aq : ∀ h : H, (a h).hom ≫ q = q) (L : X.Modules) :
    ∃ (lin : ∀ g : H,
        (tensorPullback (a g).hom).obj (pencilOrbitBundle a L) ≅ pencilOrbitBundle a L)
      (linPow : ∀ (d : ℕ) (g : H),
        (tensorPullback (a g).hom).obj ((pencilOrbitBundle a L).tensorPow d) ≅
          (pencilOrbitBundle a L).tensorPow d),
      (lin 1).hom = (orbitLinearizationUnit a a_one (pencilOrbitBundle a L)).hom ∧
      (∀ g h : H, (lin (g * h)).hom =
        (orbitLinearizationComp a a_mul (pencilOrbitBundle a L) g h).hom ≫
          (tensorPullback (a h).hom).map (lin g).hom ≫ (lin h).hom) ∧
      (∀ d : ℕ, (linPow d 1).hom =
        (orbitLinearizationUnit a a_one ((pencilOrbitBundle a L).tensorPow d)).hom) ∧
      (∀ (d : ℕ) (g h : H), (linPow d (g * h)).hom =
        (orbitLinearizationComp a a_mul ((pencilOrbitBundle a L).tensorPow d) g h).hom ≫
          (tensorPullback (a h).hom).map (linPow d g).hom ≫ (linPow d h).hom) ∧
      (∀ (T : Y.Opens) (s : Γ(L, q ⁻¹ᵁ T)) (g : H),
        (lin g).hom.app (q ⁻¹ᵁ T)
          (orbitInvariantPullback (a g).hom (pencilOrbitBundle a L) (q ⁻¹ᵁ T)
            (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g))
            (orbitTensorFrame a L (q ⁻¹ᵁ T)
              (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s)) =
          orbitTensorFrame a L (q ⁻¹ᵁ T)
            (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s) ∧
      (∀ (d : ℕ) (T : Y.Opens) (s : Γ(L, q ⁻¹ᵁ T)) (g : H),
        (linPow d g).hom.app (q ⁻¹ᵁ T)
          (orbitInvariantPullback (a g).hom ((pencilOrbitBundle a L).tensorPow d)
            (q ⁻¹ᵁ T) (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g))
            (orbitPowerSection (pencilOrbitBundle a L) (q ⁻¹ᵁ T) d
              (fun _ ↦ orbitTensorFrame a L (q ⁻¹ᵁ T)
                (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s))) =
          orbitPowerSection (pencilOrbitBundle a L) (q ⁻¹ᵁ T) d
            (fun _ ↦ orbitTensorFrame a L (q ⁻¹ᵁ T)
              (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s)) := by sorry

end AlgebraicGeometry.Scheme.Modules
