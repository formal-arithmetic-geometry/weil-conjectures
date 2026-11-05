/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteLevelProEtaleBaseChange
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement

/-!
# The four finite-level arrows

Source: blueprint, proper base change, four finite-level arrows, order 1343;
Stacks Project Tags 07A7, 09C9, 0B56 and 0944 (blueprint: def-weil-pbc-four-arrows).

The horizontal arrows and the finite exchange are isomorphisms. The reduced ambient
exchange is a morphism; neither its invertibility nor commutativity of this square is
part of this definition. All scalar extensions and pullbacks are uncompleted.

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [instance] AdicCoefficientDatum.finiteProjection_isIso

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

-- Keep coefficient transport outside the expanded exchange term. In particular, generalize
-- the ring sheaves before specializing from the function presentation to the quotient tower.

end AlgebraicGeometry.Scheme
