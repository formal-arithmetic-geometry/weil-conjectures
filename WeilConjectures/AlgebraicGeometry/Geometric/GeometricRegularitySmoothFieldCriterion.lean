/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent

/-!
# Geometric regularity and smoothness over a field

Source: Stacks Project, Varieties, Tags 038X (lemma-geometrically-regular-smooth)
and 038T (definition-geometrically-regular).
(blueprint: lem-weil-pbc-geometric-regularity-smooth-field-criterion)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
