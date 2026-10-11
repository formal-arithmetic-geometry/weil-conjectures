/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.Topology.SetsExtensionByEmpty
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Topology.Bases
import Mathlib.Order.Directed

/-!
# Directed presentations of sheaves by finite coequalizers

Source: Stacks Project, Modules, Lemma 0CAI and Equation 17.19.2.1
(blueprint: lem-weil-pbc-sheaf-directed-colimit-finite-coequalizers).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Every sheaf of sets on a space with a basis of quasi-compact opens is a directed
colimit of coequalizers of pairs of morphisms between finite coproducts of extensions
by the empty set of finite constant sheaves on basis opens.
Source: Stacks Project, Modules, Lemma 0CAI and Equation 17.19.2.1
(blueprint: lem-weil-pbc-sheaf-directed-colimit-finite-coequalizers).

Proof:
1. By `lem-weil-pbc-sheaf-basis-surjection` (0CAH), choose an epimorphism to `F` from
   a coproduct of `extensionByEmptyConstant U S`, with basis opens `U` and finite `S`.
   The adjunction and stalk description of
   `lem-weil-pbc-sets-extension-by-empty-adjunction` prove surjectivity on stalks.
2. Apply the same basis-surjection lemma to the kernel pair of this epimorphism.
   By `lem-weil-pbc-sheaf-surjection-kernel-pair-coequalizer`, the composite maps from
   that coproduct to the first coproduct have `F` as their coequalizer.
3. For each finite subfamily of relations, both maps factor through a common finite
   subcoproduct of generators, by `lem-weil-pbc-sheaf-finite-relation-truncations`.
   This uses `lem-weil-pbc-sheaves-directed-colimit-sections` on the quasi-compact
   relation opens (009F), then takes the union of the two finite supports.
4. Order the finite relation truncations and generator supports by enlargement.
   They form a nonempty directed set; the corresponding finite coequalizers form
   a functor with a compatible cocone to `F`. Every relation occurs at some stage.
   By `lem-weil-pbc-sheaf-finite-truncation-colimit`, this cocone is a colimit:
   the induced comparison is locally surjective and locally injective, hence an
   isomorphism. Colimits and coequalizers have the universal property of
   `def-weil-pbc-category-colimit`. -/
theorem exists_directedColimit_finiteCoequalizers
    (X : TopCat.{u}) (B : Set (Opens X))
    (hBasis : IsTopologicalBasis ((fun U : Opens X ↦ (U : Set X)) '' B))
    (hCompact : ∀ U ∈ B, IsCompact (U : Set X)) (F : X.Sheaf (Type u)) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Sheaf (Type u)) (c : D ⟶ (Functor.const I).obj F),
      Nonempty (IsColimit (Cocone.mk F c)) ∧
      ∀ i : I, ∃ (m n : ℕ) (U : Fin n → Opens X) (V : Fin m → Opens X)
        (S : Fin n → Type u) (T : Fin m → Type u),
        (∀ a : Fin n, U a ∈ B) ∧ (∀ b : Fin m, V b ∈ B) ∧
        (∀ a : Fin n, Finite (S a)) ∧ (∀ b : Fin m, Finite (T b)) ∧
        ∃ (β γ : (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
            (fun b : Fin m ↦ extensionByEmptyConstant (V b) (T b))) ⟶
            (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
            (fun a : Fin n ↦ extensionByEmptyConstant (U a) (S a))))
          (q : (sigmaObj (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
            (fun a : Fin n ↦ extensionByEmptyConstant (U a) (S a))) ⟶ D.obj i)
          (h : β ≫ q = γ ≫ q),
          Nonempty (IsColimit (Cofork.ofπ q h)) := by
  sorry

end TopCat
