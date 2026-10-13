/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.FiniteTorDimension

/-! # Local finite Tor dimension of a proper relatively flat single-module direct image

Source: Stacks Project, Tag 0A1H, single-module case; Tags 08CG and 08CI.
(blueprint: lem-pc-proper-flat-single-local-finite-tor).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On each affine base open the restricted direct image has a finite Tor interval.
The interval may depend on the neighbourhood. This supplies no finite-free model
and asserts no pseudo-coherence.
Source: Stacks Project, Tag 0A1H with E=O_X and G=F[0]; Tags 01XD, 08CG, 08CI.
(blueprint: lem-pc-proper-flat-single-local-finite-tor).

Proof: On the supplied affine open U, properness makes its inverse image
quasi-compact and separated. Choose a finite affine cover of that inverse image.
The alternating Cech section complex is bounded in degrees [0,d]; intersections
are affine and its section modules are flat over the ring of U by relative
flatness. Associate module sheaves on U. This gives a bounded complex of flat
quasi-coherent sheaves representing the restricted direct image, by affine
acyclicity and the Cech-to-derived comparison. A bounded flat complex is K-flat.
Tensoring it with any module in degree zero has zero terms, hence zero homology,
outside [0,d]. Thus the same interval works for every test module, as required
by finite Tor dimension. Transport the representing isomorphism from the
K-injective computation to the supplied target localization using uniqueness of
localization; its terms, flatness and vanishing are unchanged. Empty inverse images
and zero modules give the zero complex with interval [0,0].
-/
theorem properFlat_single_local_hasFiniteTorDimension
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f)
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    U.toScheme.HasFiniteTorDimension ((schemeOpenRestriction S U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)))  := by sorry

end AlgebraicGeometry
