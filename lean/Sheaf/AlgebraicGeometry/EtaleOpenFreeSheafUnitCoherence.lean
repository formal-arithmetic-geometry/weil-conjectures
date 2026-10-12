/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Identity-generator coherence for nested open subschemes

Source: Stacks Project, Tag 03F3, and the open-restriction adjunction unit calculation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The identity generator restricts to the inclusion generator on a smaller open.
Source: Stacks Project, Tag 03F3, localization restriction; the explicit adjunction
unit calculation in open_restriction_pullback_unit.
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-coherence)

Proof: Apply the constant-sheaf adjunction at the terminal object of V to both sides.
On the left, etaleOpenFreeSheafUnit V is the identity generator of the free sheaf
at V. The free-representable map sends this generator to the inclusion V to U.
On the right, the constant pullback comparison sends 1 to 1, and pulling back the
identity generator at U gives the same inclusion generator over V. To check this
with the specified inverse-image comparisons, apply open_restriction_pullback_unit
with g equal to U.ι and W equal to V. The fibre product V times_X U identifies
with V, since V is contained in U and U.ι is a monomorphism. The identity unit
cancels against the identity comparison. The inverse-image composition unit equation
then identifies the two successive restriction comparisons with the direct one.
Naturality of sheafification and of the free functor sends the generator associated
to the identity of V to the generator associated to X.homOfLE h. Thus both sides
classify the same section, and the adjunction bijection proves the equality.
This calculation is valid for equal opens and for the empty open as well. -/
theorem etaleOpenFreeSheafUnit_coherence {X : Scheme.{u}}
    (U V : X.Opens) (h : V ≤ U) :
    etaleOpenFreeSheafUnit V ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} V.ι).map
          ((etaleOpenFreeSheaf X).map
            (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk U.ι)
              (X.homOfLE h) (X.homOfLE_ι h) trivial)) ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
          (X.homOfLE_ι h).symm).hom.app
            ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)) =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (X.homOfLE h)).inv.app
        (AddCommGrpCat.of (ULift ℤ))) ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} (X.homOfLE h)).map
        (etaleOpenFreeSheafUnit U) := by sorry

end AlgebraicGeometry
