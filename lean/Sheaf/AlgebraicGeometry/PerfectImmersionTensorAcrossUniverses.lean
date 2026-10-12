/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula

/-! # The perfect immersion tensor formula in independent derived universes

Source: Stacks Project, Tag 0A9U, and uniqueness of localization, Tag 05RU.
(blueprint: lem-sc-perfect-immersion-tensor-across-universes).
-/

@[expose] public section

set_option autoImplicit false

universe u wZ wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The tensor formula for a specified right adjoint of a perfect proper closed immersion.
Source: Stacks Project, Tag 0A9U, the second equality of Tag 0BRT, and Tag 05RU.
(blueprint: lem-sc-perfect-immersion-tensor-across-universes).

Proof: compare the localizations on Z and Y with their standard localizations via
`schemeDerivedStandardEquivalence`. Their composites with Qh are isomorphic to the
standard Qh, by `Localization.compUniqFunctor`. Homology factors through Qh and hence
commutes with these equivalences, by uniqueness of localization lifts. Thus they restrict
to equivalences of the full quasi-coherent subcategories. The same argument for the
single functors identifies the supplied OP with the standard structure single object.
On K-flat representatives the transported tensor is the standard tensor: both tensors
are represented by termwise tensor of K-flat complexes, and the comparison maps descend
through localization. In particular the unit comparison is invertible. The direct-image
comparison follows by uniqueness of the right derived functor of module pushforward;
conjugating the given adjunction by the restricted equivalences then gives a right adjoint
of the standard restricted direct image. Uniqueness of right adjoints identifies this
adjoint with the one used in the tensor formula, for the supplied preservation witness.
A closed immersion has exact module pushforward. Consequently its derived pushforward
of the tensor unit is isomorphic to the single of its pushforward of O_Z. Transport the
perfection hypothesis to the standard category, using the comparisons of restrictions
and single functors on every open of Y. Apply `smooth_proper_diagonal_tensor_formula`
to i in the standard universe, at the image of K. The asserted invertible mate gives an
isomorphism from the tensor of the pulled-back K and c(O_Y) to c(K), after inclusion in
D(Z). Transport this isomorphism back, use the definition of the mixed-universe pullback,
and map the structure-object comparison through c. Invert to obtain the displayed
orientation. No smoothness or flatness is used: perfection of i_*O_Z is the required
finite Tor condition. Identity immersions give the tensor unitor; the empty scheme has
only zero objects, so the statement also holds there. -/
theorem perfectImmersion_tensor_acrossUniverses
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsProper i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))))
    (hRi : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E.obj))
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adjC : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRi ⊣ c)
    (OP : schemeDerivedQCohCategory Y)
    (hOP : OP.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf))
    (K : schemeDerivedQCohCategory Y) :
    Nonempty ((c.obj K).obj ≅
      (derivedPullbackAcrossUniverses i).obj K.obj ⊗ (c.obj OP).obj) := by sorry

end AlgebraicGeometry
