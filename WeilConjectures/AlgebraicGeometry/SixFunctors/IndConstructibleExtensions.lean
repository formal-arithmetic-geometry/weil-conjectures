/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtOneExtensionClassification
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
import Mathlib.Order.CompletePartialOrder

/-!
# Extensions of ind-constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart,
`sk-prop-ind-heart-extensions.md` and its proof (blueprint: det-ind-heart-extensions).

The two coefficient cases use the existing finite constant-model constructibility predicate.
IndCons is `ObjectProperty.ind.{u + 1}` in the internal-module category itself, with small
filtered presentations and closure under isomorphisms. No abstract ind-category replaces
this ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
