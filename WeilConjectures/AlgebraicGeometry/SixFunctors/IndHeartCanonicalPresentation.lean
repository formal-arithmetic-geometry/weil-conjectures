/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Canonical presentations of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`sk-prop-ind-heart-canonical-presentation.md` and its proof
(blueprint: det-ind-heart-canonical-presentation).

`CostructuredArrow` is exactly the category of constructible modules mapping to B.
`Functor.isDenseAt` asserts the colimit property for its tautological cocone, whose
leg at (C,c) is c. Small diagrams and essential smallness use universe u+1, as in
`IndHeartFullFaithfulnessAssertions` and def-weil-size-convention. The universal property
over the full essentially small category is equivalent to the one over a small skeleton.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
