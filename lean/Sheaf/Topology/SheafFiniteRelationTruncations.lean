/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Topology.SetsExtensionByEmpty
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Bases

/-!
# Finite support of relations between coproducts of open constant sheaves

Source: Stacks Project, Modules, proof of Lemma 17.19.2 (Tag 0CAI)
(blueprint: lem-weil-pbc-sheaf-finite-relation-truncations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- A map restricted to finitely many source summands factors through finitely many target
summands. The inclusion maps are induced by the coprojections.
Source: Stacks Project, Modules, proof of Lemma 17.19.2 (Tag 0CAI)
(blueprint: lem-weil-pbc-sheaf-finite-relation-truncations).

Proof:
1. The target coproduct is the directed colimit of its finite subcoproducts, with injective
   transition maps on sections (lem-weil-pbc-sheaf-coproduct-finite-subcoproducts).
   The inclusions compose by the universal property (def-weil-pbc-category-colimit).
2. Sections over a quasi-compact basis open come from some finite stage
   (lem-weil-pbc-sheaves-injective-directed-colimit-qc-sections).
3. Maps from an extended constant sheaf on V to G correspond naturally to maps T → G(V),
   by lem-weil-pbc-sets-extension-by-empty-adjunction and
   lem-weil-pbc-constant-sheaf-open-maps-sections.
4. Apply step 2 to each section indexed by b in B' and t in T b. The union of their finite
   supports is finite, since B' and each T b are finite. Enlarge the lifts to that union.
   Step 3 and its naturality give a lift of each summand map.
5. Assemble these lifts by the coproduct universal property; equality follows by checking
   each coprojection (def-weil-pbc-category-colimit). For two maps, take the union of their
   supports and compose both lifts with the inclusions into that union. -/
theorem extensionByEmptyConstant_finite_support
    (X : TopCat.{u}) (basis : Set (Set X)) (hbasis : IsTopologicalBasis basis)
    (hcompact : ∀ W ∈ basis, IsCompact W)
    (A B : Type u) (U : A → Opens X) (V : B → Opens X)
    (hU : ∀ a, (U a : Set X) ∈ basis) (hV : ∀ b, (V b : Set X) ∈ basis)
    (S : A → Type u) (T : B → Type u) [∀ a, Finite (S a)] [∀ b, Finite (T b)]
    (h : (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
        (fun b : B ↦ extensionByEmptyConstant (V b) (T b))) ⟶
      (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
        (fun a : A ↦ extensionByEmptyConstant (U a) (S a))))
    (B' : Set B) (hB' : B'.Finite) :
    ∃ (A' : Set A), A'.Finite ∧
      ∃ g : (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
        (fun b : ↥B' ↦ extensionByEmptyConstant (V b.val) (T b.val))) ⟶
        (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
          (fun a : ↥A' ↦ extensionByEmptyConstant (U a.val) (S a.val))),
        g ≫ Sigma.desc (fun a : ↥A' ↦
          Sigma.ι (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
            (fun a : A ↦ extensionByEmptyConstant (U a) (S a)) a.val) =
          Sigma.desc (fun b : ↥B' ↦
            Sigma.ι (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
              (fun b : B ↦ extensionByEmptyConstant (V b) (T b)) b.val) ≫ h := by
  sorry

/-- Two maps restricted to the same finite source subcoproduct factor through a common
finite target subcoproduct.
Source: Stacks Project, Modules, proof of Lemma 17.19.2 (Tag 0CAI)
(blueprint: lem-weil-pbc-sheaf-finite-relation-truncations).

Proof:
1. The target coproduct is the directed colimit of its finite subcoproducts, with injective
   transition maps on sections (lem-weil-pbc-sheaf-coproduct-finite-subcoproducts).
   The inclusions compose by the universal property (def-weil-pbc-category-colimit).
2. Sections over a quasi-compact basis open come from some finite stage
   (lem-weil-pbc-sheaves-injective-directed-colimit-qc-sections).
3. Maps from an extended constant sheaf on V to G correspond naturally to maps T → G(V),
   by lem-weil-pbc-sets-extension-by-empty-adjunction and
   lem-weil-pbc-constant-sheaf-open-maps-sections.
4. Apply step 2 to each section indexed by b in B' and t in T b. The union of their finite
   supports is finite, since B' and each T b are finite. Enlarge the lifts to that union.
   Step 3 and its naturality give a lift of each summand map.
5. Assemble these lifts by the coproduct universal property; equality follows by checking
   each coprojection (def-weil-pbc-category-colimit). For two maps, take the union of their
   supports and compose both lifts with the inclusions into that union. -/
theorem extensionByEmptyConstant_common_finite_support
    (X : TopCat.{u}) (basis : Set (Set X)) (hbasis : IsTopologicalBasis basis)
    (hcompact : ∀ W ∈ basis, IsCompact W)
    (A B : Type u) (U : A → Opens X) (V : B → Opens X)
    (hU : ∀ a, (U a : Set X) ∈ basis) (hV : ∀ b, (V b : Set X) ∈ basis)
    (S : A → Type u) (T : B → Type u) [∀ a, Finite (S a)] [∀ b, Finite (T b)]
    (h₁ h₂ : (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
        (fun b : B ↦ extensionByEmptyConstant (V b) (T b))) ⟶
      (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
        (fun a : A ↦ extensionByEmptyConstant (U a) (S a))))
    (B' : Set B) (hB' : B'.Finite) :
    ∃ (A' : Set A), A'.Finite ∧
      ∃ g₁ g₂ : (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
        (fun b : ↥B' ↦ extensionByEmptyConstant (V b.val) (T b.val))) ⟶
        (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
          (fun a : ↥A' ↦ extensionByEmptyConstant (U a.val) (S a.val))),
        (g₁ ≫ Sigma.desc (fun a : ↥A' ↦
          Sigma.ι (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
            (fun a : A ↦ extensionByEmptyConstant (U a) (S a)) a.val) =
          Sigma.desc (fun b : ↥B' ↦
            Sigma.ι (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
              (fun b : B ↦ extensionByEmptyConstant (V b) (T b)) b.val) ≫ h₁) ∧
        (g₂ ≫ Sigma.desc (fun a : ↥A' ↦
          Sigma.ι (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
            (fun a : A ↦ extensionByEmptyConstant (U a) (S a)) a.val) =
          Sigma.desc (fun b : ↥B' ↦
            Sigma.ι (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
              (fun b : B ↦ extensionByEmptyConstant (V b) (T b)) b.val) ≫ h₂) := by
  sorry

end TopCat
