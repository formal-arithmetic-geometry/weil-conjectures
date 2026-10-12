/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Construction of the formal push-pull comparison

Source: Stacks Project, Cohomology of Schemes, Lemma 088B, first half of the proof.
(blueprint: lem-weil-pbc-formal-systems-push-pull-comparison)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The adjunction maps factor through the completed proper pushforward. The first
identity characterizes the quotient comparison `κ`, and the second characterizes `α`.
There is no exceptional ideal or annihilation assertion in this construction.

Source: Stacks Project, Lemma 088B, proof up to the definition of the limit comparison.
(blueprint: lem-weil-pbc-formal-systems-push-pull-comparison)

Proof: The coherence hypothesis makes its completion a coherent formal module. At level n+1,
the pushforward of the quotient projection kills J^(n+1), since this ideal acts
through (J.comap f)^(n+1) on the target. The cokernel universal property gives
κ_n; cancellation of quotient projections gives compatibility with transitions.
The adjunction unit followed by the pushforward of β_n gives compatible maps γ_n.
On each affine open the degree-zero theorem on formal functions identifies the
inverse limit of κ with an isomorphism from the completion of the sections of f_*F.
The affine equivalence for coherent formal modules turns its inverse composed
with the limit of γ into a formal-system map α. The limit projections are
surjective, so κ_n α_n = γ_n, and this equation uniquely determines α on an
affine open. Restricting to a smaller affine open preserves the equations and
therefore the map. Glue the component sheaf maps on the affine basis; their
transition identities and the two asserted equations hold locally, hence globally.
-/
theorem exists_formalSystemsPushPull_comparison {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj)) :
    ∃ κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
          formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f,
        ∃ α : G ⟶ (completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
          (∀ n : ℕ,
            formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
              κ.app (op n) =
            (Scheme.Modules.pushforward f).map
              (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) ∧
          (∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
            adj.unit.app (G.obj.obj (op n)) ≫
              (Scheme.Modules.pushforward f).map (β.hom.app (op n))) := by
  sorry

end AlgebraicGeometry
