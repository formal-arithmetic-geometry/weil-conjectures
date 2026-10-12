/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
public import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Constancy of compatible finite-descent stalk coordinates

Source: Stacks Project, Étale Cohomology, Lemma 09Z2 and Remark 09Z3.
(blueprint: lem-weil-pbc-sets-finite-descent-coordinates-constant).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Compatible comparison pullbacks give equal coordinates at any two geometric lifts.
Source: Stacks Project, Étale Cohomology, Lemma 09Z2, last paragraph, and Remark 09Z3.
(blueprint: lem-weil-pbc-sets-finite-descent-coordinates-constant).

Proof: The inverse-image stalk bijection identifies the restriction of the stalk unit
at every lift with the identity. Hence any bijective coordinate identification satisfying
`hdiag` is the inverse of that restriction, so agrees with the germ-compatible
identification of Tag 03Q1 (3). For two lifts t and v, their pair gives a geometric
point of X' ×_X X' by the pullback universal property. Pull the equality of comparison
sections to its germ. The composition-unit formula of the inverse-image comparison
identifies the first germ with the coordinate at t and the second with the coordinate
at v. To justify this for arbitrary germs, represent their image under the bijective
inverse-image stalk comparison by a germ of a section of G; the germ formula represents
the original germ by the unit of that section. The composition-unit formula applies
on this representative. Naturality of germs under the fibre-product pasting isomorphism
and transport along the pullback condition identify the two ambient stalks. Applying
the composite inverse-image stalk comparison to the compatible germs therefore gives
the asserted equality. No lift is chosen: if the fibre is empty the assertion is
vacuous, and it also holds for the empty sheaf because there is then no section s'. -/
theorem finiteSurjectiveSetDescent_coordinates_constant
    {X X' : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (c : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x},
      (Scheme.pointSmallEtale t.1).sheafFiber.obj ((Scheme.etaleSetPullback f).obj G) →
        (Scheme.pointSmallEtale x).sheafFiber.obj G)
    (hc : ∀ t, Function.Bijective (c t))
    (hdiag : ∀ t a, c t ((colimit.pre
          ((CategoryOfElements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op) ((Scheme.pointSmallEtale x).sheafFiber.map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (X'.smallGrothendieckTopology @Etale)).unit.app G) a)) = a)
    (s' : ((Scheme.etaleSetPullback f).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
        (Scheme.Etale.mk (𝟙 X)))))
    (hs :
        etaleSetDescentComparison f (pullback.fst f f) G (Scheme.Etale.mk (𝟙 X)) s' =
          eqToHom (congrArg
            (fun k : pullback f f ⟶ X ↦ ((Scheme.etaleSetPullback k).obj G).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := f) (g := f)).symm)
            (etaleSetDescentComparison f (pullback.snd f f) G
              (Scheme.Etale.mk (𝟙 X)) s'))
    (z : (Scheme.pointSmallEtale x).fiber.obj (Scheme.Etale.mk (𝟙 X))) :
    ∀ t v : {t : Spec (.of Ω) ⟶ X' // t ≫ f = x},
      c t ((colimit.pre
          ((CategoryOfElements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x t).op)
        ((Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X)) z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology X'.smallEtaleTopology).obj
          ((Scheme.etaleSetPullback f).obj G)).obj s')) =
      c v ((colimit.pre
          ((CategoryOfElements.π (Scheme.pointSmallEtale v.1).fiber).op ⋙
            ((Scheme.etaleSetPullback f).obj G).obj)
          (Etale.baseChangeNbhd f x v).op)
        ((Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 X)) z
      ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology X'.smallEtaleTopology).obj
          ((Scheme.etaleSetPullback f).obj G)).obj s')) := by sorry

end AlgebraicGeometry
