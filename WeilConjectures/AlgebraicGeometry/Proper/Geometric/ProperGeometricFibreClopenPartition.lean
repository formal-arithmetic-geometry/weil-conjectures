/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SteinFiniteFibresResidueFields
import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibreEtaleSplitting
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFibreConnectedPreimage

/-!
# An étale clopen partition adapted to a proper geometric fibre

Source: Stacks Project, More on Morphisms, Tag 0BUI, proof of
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`, Stein splitting paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
