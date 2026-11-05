/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ArrowExactColimits
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Kernels and cokernels of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
sk-prop-ind-heart-kernels-cokernels.md and its proof
(blueprint: det-ind-heart-kernels-cokernels).

The square category is `CostructuredArrow ι.mapArrow (Arrow.mk f)`, where ι is the
constructible inclusion. Its tautological arrow cocone is Mathlib's pointwise left
extension cocone. Applying `ker` and `coker` gives exactly the canonical cocones at
ker(f) and coker(f); asserting their colimit properties fixes the comparisons themselves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
