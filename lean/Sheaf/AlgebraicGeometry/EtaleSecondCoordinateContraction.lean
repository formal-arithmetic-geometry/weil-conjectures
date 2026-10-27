/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G5
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData

/-! # The second coordinate contraction for a symmetric coefficient

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sfb-etale-second-coordinate-contraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

/-- The second-coordinate contraction for any coefficient with identity self symmetry.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle before
using the diagonal integral; Stacks Tags 07A7 and 0B56.
(blueprint: lem-sfb-etale-second-coordinate-contraction).

Proof: apply lem-weil-pbc-ringed-exchange-tensor-coherence to the self-product square,
transported through the normalized ringed/module-sheaf comparisons. Invert its square:
the pullback of inverse f projection, followed by inverse exchange, is inverse p2
projection followed by the tensor pullback comparison and inverse exchange on f*L.
Tensor with f*L. Use lem-sfb-ringed-projection-tensor-composition to reassociate the
two tensor extractions. The coordinate comparison on HK is the pullback tensor
comparison conjugated by fp1=fp2, exactly coordinateH. Transport hL by the braided
pullback comparisons to see that interchanging the two copies of L_W is identity.
Naturality of symmetry with respect to the trace moves that trace onto the remaining
kernel factor. Substitute ht, which identifies the pulled-back trace with the p2 trace
under exchange and coordinate. The normalized tensor unit comparison and right
unitors then give precisely the displayed formula. This step neither uses t1 nor
the first coordinate equation and makes no reference to a diagonal class. -/
theorem secondCoordinateContraction [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (hL : (swap A Y L L).hom = 𝟙 _)
    (t : (push A f).obj ((pull A f).obj L) ⟶ constantComplex A Y)
    (t2 : (push A (pullback.snd f f)).obj
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L)) ⟶ constantComplex A X)
    (ht : (exchange2 A f ((pull A f).obj L)).hom ≫
        (push A (pullback.snd f f)).map (coordinate A f L).hom ≫ t2 =
      (pull A f).map t ≫ (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom) :
    ∀ K : DerivedCategoryModule A Y,
        (comparison A f L ((H A f L).obj K)).hom ≫
            (H A f L).map
              (evaluation A f L t K) =
          (push A (pullback.snd f f)).map
              (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
                (coordinateH A f L K).hom).app
                  ((pull A (pullback.snd f f)).obj ((pull A f).obj L))) ≫
            (orderedProjectionIso A (pullback.snd f f) ((H A f L).obj K)
              ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).inv ≫
                ((derivedTensor (ModuleCat.{u + 1} A) X).obj
                  ((H A f L).obj K)).map t2 ≫
                  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
                    ((H A f L).obj K)).hom := by
  sorry

end AlgebraicGeometry.Etale.CoordinateTrace
