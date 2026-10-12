/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Equality of projection pullbacks after restriction to the closed fibre

Source: Stacks Project, Tag 09ZF, proof of lemma-gabber-h0, third paragraph
and fourth paragraph's parenthetical comparison on Z' times_Z Z'
(blueprint: lem-weil-pbc-gabber-h0-projection-restrictions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A compatible section has equal projection pullbacks after restriction.
Source: Stacks Project, Tag 09ZF, proof of lemma-gabber-h0, third paragraph
and fourth paragraph: "this is true for the pullbacks of t'"
(blueprint: lem-weil-pbc-gabber-h0-projection-restrictions).

Proof:
Put Y = X' times_X X', a = p_1 followed by h = p_2 followed by h,
and D = Z times_X Y with j : D to Y. Put Z' = Z times_X X' and k : Z' to X'.
For each projection p_r : Y to X', the pullback property gives q_r : D to Z'
with q_r followed by k = j followed by p_r and q_r followed by (Z' to Z)
equal to the projection D to Z. Apply the unit along q_r to hres. Naturality
in the sheaf and the unit-compatible composition isomorphisms identify its
right side with the restriction along j of the p_r-pullback of s', transported
to a^*F. More explicitly, after comparison to the composite inverse image,
this section equals c_(h,p_r j)((p_r j)^*s') = c_(h,k q_r)((k q_r)^*s').
Composition associativity rewrites it as the pullback along q_r of
c_(h,k)(k^*s'). By hres this is the pullback along q_r of
c_(i,Z' to Z)((Z' to Z)^*t), hence equals c_(i,D to Z)((D to Z)^*t).
This is independent of r. The fibre-product pasting maps agree because their
projections agree. The composition comparison is an isomorphism, so cancel
it to obtain equality under the raw unit along j, as stated. The transport
for p_2 is exactly eqToHom along pullback.condition.symm; all other transports
come from the same projection equalities. No closed-immersion, finiteness,
surjectivity, or injectivity assumption is used. Identity and empty schemes
are allowed: this calculation only uses the pullback universal property. -/
theorem gabber_h0_projection_restrictions
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s' : ((Scheme.etaleSetPullback h).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X)))))
    (hres : etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t =
        eqToHom (congrArg
          (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X)) s')) :
    let a : pullback h h ⟶ X := pullback.fst h h ≫ h
    let j : pullback i a ⟶ pullback h h := pullback.snd i a
    let G := (Scheme.etaleSetPullback a).obj F
    let U := (MorphismProperty.Over.pullback @Etale ⊤ a).obj (Scheme.Etale.mk (𝟙 X))
    etaleSetDescentUnit j G U
      (etaleSetDescentComparison h (pullback.fst h h) F (Scheme.Etale.mk (𝟙 X)) s') =
    etaleSetDescentUnit j G U
      (eqToHom (congrArg
          (fun k : pullback h h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := h) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd h h) F (Scheme.Etale.mk (𝟙 X)) s')) := by
  sorry

end AlgebraicGeometry
