/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.Topology.AbelianOpenExtensionByZero
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Stalks
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Zero locus of a section of a locally constant sheaf

Source: the blueprint of the Weil conjectures, chapter `sec-proper-base-change`, unit
`sk-thm-iff`, `lemma-weil-pbc-spectral-restriction`, detailed form, Step 1
(blueprint: lem-weil-pbc-locally-constant-zero-locus-clopen); Stacks Project, Sheaves,
Example 007B and Lemma 007Z for the stalks of a constant sheaf.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- (blueprint: lem-weil-pbc-locally-constant-zero-locus-clopen) Let `T` be a topological space
and `F` a sheaf of abelian groups on `T` that is *locally constant*: every point `x` has an open
neighbourhood `U` such that the restriction `F|_U` (`abelianOpenRestriction U F`, the sheaf
`W ↦ F(W)` on the opens of `U`) is isomorphic to the constant sheaf on `U` of some abelian
group `A`. For a global section `s`, the zero locus `Z(s) = {x | s_x = 0}` of its germs is open
and closed in `T` (blueprint, `lemma-weil-pbc-spectral-restriction`, detailed form, Step 1).

Proof. (1) `Z(s)` is open, for every sheaf of abelian groups: if `s_x = 0`, the description of
equality of germs (def-weil-pbc-module-stalk) gives an open `W ∋ x` with `s|_W = 0`, and then
`s_y = 0` for all `y ∈ W`.
(2) Stalks of a constant sheaf: for a space `U`, an abelian group `A`, the constant presheaf
`P` and its sheafification `θ : P ⟶ A_U` (def-weil-pbc-constant-sheaf,
def-weil-pbc-sheafification), the map `c_y : A → (A_U)_y`, `e ↦ θ_W(e)_y`, is an isomorphism
for every `y ∈ U`: the germ map `A = P(U) → P_y` is bijective (Stacks, Example 007B) and
`θ_y` is an isomorphism by lem-weil-pbc-stalk-sheafification-space (Stacks, Lemma 007Z).
(3) Local structure: let `x ∈ T`, choose `U ∋ x`, `A` and `φ : F|_U ≅ A_U`. For `y ∈ U` the
stalk of `F|_U` at `y` is `F_y` (the opens inside `U` are cofinal), and `φ_y` is an
isomorphism. Put `t = φ_U(s|_U)`. By (2) there is a unique `e ∈ A` with `t_x = c_x(e)`, hence
an open `W` with `x ∈ W ⊆ U` and `t|_W = θ_U(e)|_W`. For `y ∈ W`, `φ_y(s_y) = c_y(e)`, and
`φ_y`, `c_y` are injective, so `s_y = 0` iff `e = 0`: either `W ⊆ Z(s)` or `W ∩ Z(s) = ∅`.
(4) `Z(s)` is closed: for `x ∉ Z(s)` the `W` of (3) is not contained in `Z(s)`, so it is
disjoint from `Z(s)`; hence the complement is open. With (1), `Z(s)` is open and closed. -/
theorem isClopen_setOf_germ_eq_zero_of_locallyConstant {T : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (hF : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ ∃ A : AddCommGrpCat.{u},
      Nonempty (abelianOpenRestriction U F ≅
        (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat T).obj U))
          AddCommGrpCat.{u}).obj A))
    (s : F.obj.obj (op ⊤)) :
    IsClopen {x : T | F.presheaf.germ (⊤ : Opens T) x (Set.mem_univ x) s = 0} := by
  sorry

end TopCat.Sheaf
