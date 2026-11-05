/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitFibreDimensionBound

/-!
# Quasi-finiteness descends for a finitely presented affine model

Source: Stacks Project, Limits, Tag 094M (lemma-descend-quasi-finite), in Situation
081D, specialized to affine schemes
(blueprint: lem-weil-pbc-descend-quasifinite-affine).

The tensor products are expressed as pushouts in `CommRingCat`. The canonical map
from the left factor is `pushout.inl`; `CommRingCat.pushoutCoconeIsColimit` identifies
this pushout and map with the algebra tensor product and its left inclusion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
