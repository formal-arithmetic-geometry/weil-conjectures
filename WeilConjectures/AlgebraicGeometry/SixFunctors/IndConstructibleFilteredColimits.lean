/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Filtered colimits and sums of ind-constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart,
`sk-prop-ind-heart-filtered-colimits.md` and its proof
(blueprint: det-ind-heart-filtered-colimits).

The standing geometric hypotheses are those of `sk-def-sfb-dc-setting`.
`ObjectProperty.ind.{u + 1}` of `IsConstantModelConstructible` is precisely IndCons:
small filtered presentations in the actual internal-module category, closed under isomorphism.
The two statements cover respectively a finite coefficient subextension and the condensed
algebraic closure. Coproducts are stated using arbitrary colimit cofans, including the empty one.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
