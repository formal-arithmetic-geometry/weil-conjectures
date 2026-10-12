/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
import Sheaf.Topology.SheafOfModulesFromBasis

/-!
# Extending modules on an indexed basis

Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-indexed-basis)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

set_option backward.isDefEq.respectTransparency false in
/-- The basis-extension theorem with repeated representatives of the same open allowed.
Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-indexed-basis)

Proof:
1. Set B=range U and choose one index c(V) for each V in B. Give V the module Q(c(V)),
   transported along U(c(V))=V. Restriction is r between the chosen indices. The identity,
   composition and scalar laws descend to this presheaf of modules.
2. For any i,j with U i=U j, restriction in each direction is inverse to the other:
   apply composition and then identity. These inverse maps identify all representatives.
   In particular the chosen representative of an intersection identifies with cap i j.
3. The finite refinement hypothesis descends to B: index a covering by its members,
   choose an index for each, apply hrefine and take the displayed finite basis opens.
   Transport each compatible finite family to the chosen representatives. Composition
   and the inverse identifications from step 2 translate overlap equality into hglue.
   Transport its unique glued element back to obtain finite unique gluing on B.
4. Apply exists_sheafOfModules_from_basis. For each original i compose its chosen-basis
   section equivalence with the inverse representative identification of step 2 to obtain
   iota i. Composition proves its restriction law.
5. A compatible linear family psi restricts to the chosen representatives. Apply the
   basis-extension universal property to obtain its unique morphism. Composition extends
   its section formula to every original index, and uniqueness on chosen indices proves
   uniqueness on all indices. If every psi i is bijective, so is every chosen map, and
   the basis-extension isomorphism criterion applies. Empty covers are included in hglue,
   so this construction also applies to the empty space and empty basis. -/
theorem exists_sheafOfModules_from_indexed_basis
    (X : TopCat.{u}) (I : Type u) (U : I → Opens X)
    (hB : IsBasis (Set.range U))
    (cap : I → I → I) (hcap : ∀ i j, U (cap i j) = U i ⊓ U j)
    (hrefine : ∀ (i : I) (J : Type u) (V : J → I),
      (⨆ j, U (V j)) = U i →
      ∃ (n : ℕ) (W : Fin n → I), (⨆ k, U (W k)) = U i ∧
        ∀ k, ∃ j, U (W k) ≤ U (V j))
    (R : TopCat.Sheaf RingCat.{u} X)
    (Q : ∀ i : I, ModuleCat.{u} (R.obj.obj (op (U i))))
    (r : ∀ (i j : I), U j ≤ U i → Q i →+ Q j)
    (rid : ∀ (i : I) (s : Q i), r i i le_rfl s = s)
    (rcomp : ∀ (i j k : I) (hji : U j ≤ U i) (hkj : U k ≤ U j) (s : Q i),
      r j k hkj (r i j hji s) = r i k (hkj.trans hji) s)
    (rsmul : ∀ (i j : I) (h : U j ≤ U i) (a : R.obj.obj (op (U i))) (s : Q i),
      r i j h (a • s) = R.obj.map (homOfLE h).op a • r i j h s)
    (hglue : ∀ (i : I) (n : ℕ) (V : Fin n → I) (hV : ∀ j, U (V j) ≤ U i),
      (⨆ j, U (V j)) = U i → ∀ s : ∀ j, Q (V j),
      (∀ j k,
        r (V j) (cap (V j) (V k)) (by rw [hcap]; exact inf_le_left) (s j) =
        r (V k) (cap (V j) (V k)) (by rw [hcap]; exact inf_le_right) (s k)) →
      ∃! t : Q i, ∀ j, r i (V j) (hV j) t = s j) :
    ∃ (E : SheafOfModules.{u} R)
      (iota : ∀ i : I, E.val.obj (op (U i)) ≃ₗ[R.obj.obj (op (U i))] Q i),
      (∀ (i j : I) (h : U j ≤ U i) (s : E.val.obj (op (U i))),
        iota j (E.val.map (homOfLE h).op s) = r i j h (iota i s)) ∧
      (∀ (G : SheafOfModules.{u} R)
        (psi : ∀ i : I, Q i →ₗ[R.obj.obj (op (U i))] G.val.obj (op (U i))),
        (∀ (i j : I) (h : U j ≤ U i) (s : Q i),
          psi j (r i j h s) = G.val.map (homOfLE h).op (psi i s)) →
        (∃! phi : E ⟶ G, ∀ (i : I) (s : E.val.obj (op (U i))),
          phi.val.app (op (U i)) s = psi i (iota i s)) ∧
        (∀ (phi : E ⟶ G),
          (∀ (i : I) (s : E.val.obj (op (U i))),
            phi.val.app (op (U i)) s = psi i (iota i s)) →
          (∀ i : I, Function.Bijective (psi i)) → IsIso phi)) := by sorry

end TopologicalSpace.Opens
