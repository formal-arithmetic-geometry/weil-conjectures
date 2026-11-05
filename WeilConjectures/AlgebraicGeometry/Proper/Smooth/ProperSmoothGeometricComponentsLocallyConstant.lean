/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Flat.FlatProperComponentCountLowerSemicontinuous
import WeilConjectures.AlgebraicGeometry.Proper.ProperReducedGlobalSectionsProduct

/-!
# Geometric component counts in proper smooth families

Source: Stacks Project, `more-morphisms.tex`, Tag 0E0N,
`lemma-proper-flat-geom-red`, specialized to smooth morphisms
(blueprint: lem-weil-pbc-proper-flat-geometric-components-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
