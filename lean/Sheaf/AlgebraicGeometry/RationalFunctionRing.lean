/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.RationalFunctions

/-!
# The rational-function ring in arbitrary universes

Source: Stacks Project, Morphisms, Definitions 01RS, 01RT, 01RU and Lemma 01RV
(blueprint: def-sc-rational-functions).
-/

@[expose] public section

universe v

open CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The ring of rational functions on a scheme is the colimit of its section rings on
 dense opens, with transition maps given by restriction. Thus elements are section classes,
 identified when they agree on a smaller dense open; addition and multiplication are induced
 by restriction to intersections and the ring operations on sections. The existing dense-open
 diagram is reused, with the ring universe explicit. Source: Stacks Project, Tags 01RT, 01RU
 and Lemma 01RV (blueprint: def-sc-rational-functions). -/
noncomputable def rationalFunctionRing (X : Scheme.{v}) : CommRingCat.{v} :=
  colimit (denseOpenSections X)

end AlgebraicGeometry.Scheme
