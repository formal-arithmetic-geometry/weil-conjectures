/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.RelativeFlatModuleStalk
import Sheaf.Topology.InverseImageStalk
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Algebra.Homology.ModuleStalkExact

/-! # Relative flatness on an open localized site

Source: Stacks Project, Tags 01U2, 05NE and 0098.
(blueprint: lem-pc-relative-flat-open-scalar-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- Restricting an affine-locally base-flat module to an open site and restricting
scalars along the inverse-image structure map yields a flat module over that ring.
Source: Stacks Project, Tags 01U2, 05NE and 0098.
(blueprint: lem-pc-relative-flat-open-scalar-restriction).

Proof: for every point x of U, use relative_flat_module_stalk to obtain flatness of
G_x over O_S,f(x). The stalk of the inverse-image ring is canonically O_S,f(x),
and the scalar-restricted module stalk is G_x with its action induced by f.stalkMap x.
Restriction to the localized open site preserves these stalks. Under the canonical
ring and module isomorphisms its stalks are therefore flat. For an exact short complex
of modules over the inverse-image ring on U, tensor and stalk commute, so tensoring
with this module preserves exactness on every stalk. Stalks detect exactness; the
additive tensor functor consequently preserves finite limits and colimits, giving
IsFlat. No quasi-coherence is needed. If U is empty the stalk test is vacuous; the
zero module is covered by the same argument. -/
theorem relativeFlat_open_scalarRestriction
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (G : X.Modules)
    (hflat : G.IsFlatOver f) :
    let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
      (Modules.tensorPullbackRingMap f)
    let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).map α
    SheafOfModules.IsFlat ((SheafOfModules.restrictScalars B).obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj G)) := by sorry

end AlgebraicGeometry.Scheme
