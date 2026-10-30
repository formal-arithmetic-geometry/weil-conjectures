/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose

/-! # Two coordinate factorizations before applying a trace

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

/-- The two projection/exchange routes to the first-coordinate direct image agree.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle,
coordinate interchange; Stacks Tags 07A7, 0B56 and 0D6E.
(auxiliary; not a blueprint node).

Proof: present the constant-ring small etale topoi as ringed tensor corners using
lem-sfb-ringed-derived-monoidal-comparisons. Transport along the equivalence between
constant-ring modules and ModuleCat-valued sheaves. The tensor comparison is fixed on
flat K-flat representatives, the adjunction comparison by the ordinary module adjunction,
and the direct-image compositor by its composite counit equation. Thus the projection
mates are the existing rightDerivedLowerStarProjectionMap, the square mates are exchange1
and exchange2, and the direct path comparison is directComparison. Apply the first
conjunct of lem-sfb-ringed-kunneth-factorizations with q=f, a=p1, b=p2, and N=f*L.
Its first route is the ordered projection followed by the inverse of comparison;
its second is the ordinary projection, tensor exchange1, and ordered p1 projection.
Cancel the canonical symmetries. The equality of right-adjoint path comparisons follows
from the equality of their pullback mates, so it uses the specified directComparison.
No trace, line hypothesis, shift or diagonal class is involved. -/
theorem coordinateKunnethFactorization [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (M : DerivedCategoryModule A X) :
    (orderedProjectionIso A f ((push A f).obj M) ((pull A f).obj L)).hom ≫
        (push A f).map (comparison A f L M).inv ≫
        (directComparison A f).hom.app _ =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
          ((push A f).obj ((pull A f).obj L)) ≫
        (push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              (exchange1 A f ((pull A f).obj L)).hom ≫
            (orderedProjectionIso A (pullback.fst f f) M
              ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).hom) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  apply (adj.homEquiv _ _).symm.injective
  exact coordinateKunnethFactorization_transpose A f L M

end AlgebraicGeometry.Etale.CoordinateTrace
