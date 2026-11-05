/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.ProperBaseChange.FiniteMonicSplitting
import WeilConjectures.ProperBaseChange.MonicTensorPresentation.SplitMonicTensorSections
import WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeAlgebraSpectrum

/-!
# Finite affine morphisms and finite covers by closed sections

Source: Stacks Project, Morphisms, Tag 03HW, Lemma `lemma-massage-finite`, clauses (1)–(5)
(blueprint: lem-weil-pbc-finite-affine-section-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
