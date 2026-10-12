/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.EventuallyAffine
import Sheaf.Paper.DirectedColimitBaseChangeElementwise

/-!
# Eventual closed immersions in inverse systems

Source: Stacks Project, Limits, Lemma 0A0N
(blueprint: lem-weil-pbc-eventually-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- If an inverse system over a quasi-compact, quasi-separated base has closed immersion
transitions, quasi-compact and quasi-separated stages, and locally finite type structure
maps, and its limit structure map is a closed immersion, then all sufficiently late
structure maps are closed immersions.

Source: Stacks Project, Limits, Lemma 0A0N
(blueprint: lem-weil-pbc-eventually-closed-immersion).

Proof:
1. Closed immersions are affine (lem-weil-pbc-closed-immersion-integral-separated-uc).
   The eventual-affineness lemma 09ZM (lem-weil-pbc-eventually-affine) permits restriction
   to an upper tail where all structure maps are affine.
2. Choose a finite affine open cover V_j of T. The inverse images W_{j,i} and W_j in
   the stages and the limit are affine. Their rings A_{j,i} and A_j carry compatible
   maps from R_j = O_T(V_j) and compatible transition maps.
3. The transition maps of these rings and R_j → A_j are surjective by
   lem-weil-pbc-closed-immersion-affine-cover-criterion. Each R_j → A_{j,i} is of finite
   type by lem-weil-pbc-lft-affine-pairs.
4. By lem-weil-pbc-limit-cone-affine-projections-opens, the W_j are limits of the W_{j,i}.
   The affine clause of lem-weil-pbc-limit-affine-transition identifies A_j with the
   colimit of the A_{j,i}, also after restricting to any upper tail.
5. Choose finitely many R_j-algebra generators at a fixed stage. Lift their limit
   images to R_j using surjectivity. By lem-weil-pbc-directed-colimit-base-change-elementwise,
   each difference vanishes at some stage. A common upper bound kills all differences.
   Surjectivity of the transition map then makes R_j → A_{j,i} surjective at that stage
   and every later stage.
6. Choose a common upper bound for the finitely many affine opens. The affine-cover
   criterion makes its structure map a closed immersion. Later structure maps are
   composites with closed immersions and are therefore closed immersions as well. -/
theorem eventually_isClosedImmersion_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj T)
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsClosedImmersion f] :
    ∃ i : I, ∀ j : I, i ≤ j → IsClosedImmersion (h.app (op j)) := by
  sorry

end AlgebraicGeometry
