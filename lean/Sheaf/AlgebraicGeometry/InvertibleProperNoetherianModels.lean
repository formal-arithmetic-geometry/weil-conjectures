/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Order.Directed
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherian
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent

/-! # Compatible proper Noetherian models carrying an invertible module

Source: Stacks Project, More on Morphisms, Tag 0D2S, proof of
`lemma-ample-in-neighbourhood`, approximation and compatible invertible modules
(blueprint: lem-trf-invertible-proper-noetherian-models).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A proper morphism over an affine scheme, together with an invertible module on its
source, has compatible proper Noetherian models indexed by a directed partial order
with a least element. The module at each stage is pulled back from the least stage;
the displayed transition and limit isomorphisms are the composition comparisons,
transported along functoriality and the cone equation, followed by the initial
limit isomorphism in the latter case.

Source: Stacks Project, More on Morphisms, Tag 0D2S, proof of
`lemma-ample-in-neighbourhood`, through the sentence beginning `Let y_i`.
(blueprint: lem-trf-invertible-proper-noetherian-models).

Proof:
1. The affine base is quasi-compact and quasi-separated by
   `lem-weil-pbc-affine-scheme-qcqs`. Apply the affine-base clause of
   `lem-weil-pbc-proper-limit-noetherian` to obtain proper models over affine
   finite-type integer schemes, affine transitions, commuting squares and both limits.
   The original proper morphism need not be finitely presented.
2. By `lem-weil-pbc-finite-type-over-noetherian`, the base stages are Noetherian,
   since Spec Z is Noetherian, and their proper source stages are Noetherian as well.
   `lem-weil-pbc-locally-noetherian-quasi-separated` supplies quasi-separatedness.
3. Apply clause (1) of `lem-weil-pbc-limit-cone-affine-projections-opens` to both
   limit cones: all their projections are affine.
4. By `lem-trf-invertible-affine-limit-descent`, the invertible module descends
   to an invertible module at some stage c, with a pullback isomorphism to M.
5. Quotient the indexing preorder by mutual comparability, choosing representatives
   with c representing its own class. The representatives form a cofinal partial order.
   Restrict to representatives above c; this is directed with least element c.
   For any cone on this tail and any original index k, choose a tail index l above k
   and compose its leg with the transition to k. A common upper bound of two choices
   proves independence; the same argument gives compatibility and uniqueness.
   Thus tail cones extend uniquely to the original diagram, so both limits persist.
   All stage, transition and projection properties persist under this restriction.
6. Put M_i = q_i0^* M_0. The theorem
   `lem-weil-pbc-invertible-pullback-invertible` gives invertibility. Invert the
   normalized composition comparison of `def-pc-module-pullback`, and transport
   along q_ji;q_i0 = q_j0 or a_i;q_i0 = a_0. In the latter case compose with the
   descended isomorphism a_0^* M_0 ≅ M. At the least stage the identity-pullback
   comparison identifies q_00^* M_0 with M_0. These give exactly the displayed
   canonical module comparisons. -/
theorem invertible_proper_noetherian_models
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] [IsAffine X]
    (M : Y.Modules) [M.IsInvertible] :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : OrderBot I) (_ : IsDirected I (· ≤ ·))
      (Ys Xs : Iᵒᵖ ⥤ Scheme.{u}) (fs : Ys ⟶ Xs)
      (a : (Functor.const Iᵒᵖ).obj Y ⟶ Ys)
      (b : (Functor.const Iᵒᵖ).obj X ⟶ Xs),
      Nonempty (IsLimit (Cone.mk Y a)) ∧ Nonempty (IsLimit (Cone.mk X b)) ∧
      (∀ (i j : Iᵒᵖ) (h : i ⟶ j), IsAffineHom (Ys.map h) ∧ IsAffineHom (Xs.map h)) ∧
      (∀ i : Iᵒᵖ, IsAffineHom (a.app i) ∧ IsAffineHom (b.app i)) ∧
      (∀ i : Iᵒᵖ, IsProper (fs.app i)) ∧
      (∀ i : Iᵒᵖ, a.app i ≫ fs.app i = f ≫ b.app i) ∧
      (∀ i : Iᵒᵖ, IsAffine (Xs.obj i) ∧
        LocallyOfFiniteType (specULiftZIsTerminal.from (Xs.obj i)) ∧
        QuasiCompact (specULiftZIsTerminal.from (Xs.obj i))) ∧
      (∀ i : Iᵒᵖ, IsNoetherian (Xs.obj i) ∧ IsNoetherian (Ys.obj i) ∧
        QuasiSeparatedSpace (Ys.obj i)) ∧
      ∃ (M₀ : (Ys.obj (op (⊥ : I))).Modules), M₀.IsInvertible ∧
        ∃ (e₀ : (Scheme.Modules.tensorPullback (a.app (op (⊥ : I)))).obj M₀ ≅ M)
          (e : ∀ (i j : I) (hij : i ≤ j),
            (Scheme.Modules.tensorPullback (Ys.map (homOfLE hij).op)).obj
                ((Scheme.Modules.tensorPullback
                  (Ys.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀) ≅
              (Scheme.Modules.tensorPullback
                (Ys.map (homOfLE (bot_le : (⊥ : I) ≤ j)).op)).obj M₀)
          (d : ∀ i : I, (Scheme.Modules.tensorPullback (a.app (op i))).obj
              ((Scheme.Modules.tensorPullback
                (Ys.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀) ≅ M),
          (∀ i : I, ((Scheme.Modules.tensorPullback
            (Ys.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀).IsInvertible) ∧
          (∀ (i j : I) (hij : i ≤ j), e i j hij =
            ((Scheme.Modules.tensorPullbackSectionComp (Ys.map (homOfLE hij).op)
              (Ys.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).symm.app M₀) ≪≫
                eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj M₀)
                  (Ys.map_comp (homOfLE hij).op
                    (homOfLE (bot_le : (⊥ : I) ≤ i)).op).symm)) ∧
          (∀ i : I, d i =
            ((Scheme.Modules.tensorPullbackSectionComp (a.app (op i))
              (Ys.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).symm.app M₀) ≪≫
                eqToIso (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj M₀)
                  ((Cone.mk Y a).w (homOfLE (bot_le : (⊥ : I) ≤ i)).op)) ≪≫ e₀) := by
  sorry

end AlgebraicGeometry
