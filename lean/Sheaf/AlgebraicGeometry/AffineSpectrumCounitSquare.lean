/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
import Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap

/-! # The affine spectrum derived counit square

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-counit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The inverse pullback counits commute with the canonical affine coordinate comparison.
This is an equation of derived morphisms, independent of f, g, z0 and stalk cohomology.

Proof: let Pg be the termwise gprime-pullback of P and P0 the termwise isoSpec
pullback. Apply affineSpectrum_representative_map_eq with K=Q(P), Kprime=Q(Pg),
coefficient the pinned gprime counit, and Coordinates given by P, Pg, identity
representative isomorphisms and identity chain map. K-flatness is hP and represents
reduces to functoriality of identity. Choose e and eprime to be the inverse exact
iso-pullback complex counits. Their two defining equations are the explicit
quotientCompQhIso and mapHomotopyCategoryFactors formulas; the latter comparison
is identity on each complex. The resulting equation says spectrum counit followed
by Q(alpha.hom) followed by eprime.hom equals derived spectrum pullback of e.hom,
followed by the canonical derived composition comparison, followed by derived
isoSpec pullback of the gprime counit. Cancel the composition comparison and the
last counit. All four counits and alpha are invertible, so composing with their
inverses gives exactly the displayed equation. No stalk-ring comparison, localized
base-derived tensor map, coefficient to an arbitrary target, or point is involved.
For identity coordinate maps this is the identity composition law; zero complexes
and empty schemes use the same counit equations.
Source: Stacks Project, Tag 0D5S, lemma-pullback-composition; Tag 0DJ8, affine
reduction on the canonical representative.
(blueprint: lem-pc-affine-spectrum-counit-square). -/
theorem affineSpectrum_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X'] (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P)))) :
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    (derivedPullback X'.isoSpec.inv).map
        (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
      (affineSpectrumDerivedPullbackIso g').inv.app (DerivedCategory.Q.obj P) =
    (isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app Pg ≫
      DerivedCategory.Q.map (affineSpectrumTensorComplexIso g' P).inv ≫
      inv ((counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P0)) ≫
      (derivedPullback (Spec.map g'.appTop)).map
        ((isoPullbackComplexCounitIso X.isoSpec.inv).inv.app P) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
