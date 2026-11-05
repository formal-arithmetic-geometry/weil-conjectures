/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.FieldTheory.MakeSeparable
import WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent

/-!
# Perfect-closure criterion for geometric normality

Source: Stacks Project, Algebra, Tag 037Z (lemma-geometrically-normal), (4) iff (1),
and Tag 046W (lemma-perfection)
(blueprint: lem-weil-pbc-geometrically-normal-perfect-closure-criterion).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Algebra

end Algebra
