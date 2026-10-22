/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.CompletedFiniteExchangeCoordinates

/-!
# Ordinary completed-to-finite scalar compatibility

The coefficient projection intertwines the normalized ordinary inverse exchanges.
Source: Stacks Project, Modules on Sites, Tags 03DI, 03D7 and 04J0;
blueprint finite-exchange identification before derived inverse limits.
(blueprint: lem-cbc-completed-finite-scalar-exchange).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

/-- The ordinary inverse exchange commutes with the finite scalar projection.
Source: Stacks Project, Modules on Sites, lemma-extension-by-zero (03DI),
lemma-adjoint-pullback-pushforward-modules (03D7), and
lemma-localize-morphism-ringed-sites (04J0); finite-exchange identification
in the blueprint completed-extension-zero comparison, Step 8 of the parent.
(blueprint: lem-cbc-completed-finite-scalar-exchange).

Proof: transpose the square under the two composite extension/pullback adjunctions.
The source and target coordinate maps are the mates of the prescribed direct-image
and open-restriction comparisons. Mates commute with composition, so the transposed
square compares the cartesian right exchange before and after scalar restriction.
For the finite exchange, conjugate the two module pullback compositors: their
conjugates are the prescribed direct-image compositors. Equality transport commutes
with conjugation by equality induction. Thus the conjugate of moduleSquareG.inv is
moduleRComp for j-prime,g, followed by transport across the square equation and
moduleRComp for gU,j inverted. The defining section formula for moduleRComp, its
inverse identity, and presheaf functoriality identify this with restriction along
the pullback-pasting site isomorphism. The open-unit formula defining singleBetaInv
and the mates pasting law then give the finite right exchange used in this square.
The direct-image comparison is identity on sections. The open-restriction comparison
sends a pullback-unit generator along the adjoint site arrow. On such a generator,
both composites therefore restrict the original section along the same cartesian
comparison V times_U U' to V times_X X'. The projection equations identify the scalar
actions. These distinguished unit generators cover all sections: their image under
the normalized open-restriction isomorphism is the original section, and applying
its inverse expresses any section in this form. Sectionwise extensionality therefore
proves the right square. Injectivity of the mates equivalence proves the displayed left
square. This uses arbitrary finite-coefficient modules; no complexes, resolutions,
completeness, quasi-compactness, or inverse limits enter. -/
theorem cbcFiniteScalarExchange_inverse (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) U) :
    (cbcFiniteTargetRes d sq n).hom.app M ≫
      (cbcFiniteRes d X' n).map
        ((@singleBetaInv.{u} (cbcFiniteRing d n) _ U' U X' X gU j' j g
          sq.isOpenImmersion sq.isOpenImmersion' sq.w).app M) =
    (cbcUnderivedInverseExchange d sq).app ((cbcFiniteRes d U n).obj M) ≫
      (cbcFiniteSourceRes d sq n).hom.app M := by sorry

end AlgebraicGeometry.Scheme
