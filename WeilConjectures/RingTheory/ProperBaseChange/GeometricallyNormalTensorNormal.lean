/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.SmoothNormalRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Algebra.Field.ULift
import WeilConjectures.FieldTheory.SeparableSmoothColimit
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Tensor products of geometrically normal and normal algebras

Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

end Algebra
