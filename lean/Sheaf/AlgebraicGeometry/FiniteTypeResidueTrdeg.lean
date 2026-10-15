/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.ZetaSeries
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Residue fields of finite type schemes have finite transcendence degree

Source: literature/stacks-project/algebra.tex, Lemma "lemma-dimension-prime-polynomial-ring"
(Tag 00P0)
(blueprint: lem-kun-finite-type-residue-trdeg)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a scheme of finite type over a field, every residue field has finite transcendence degree.

Source: Stacks Project, Tag 00P0, applied to an affine neighbourhood of the point
(blueprint: lem-kun-finite-type-residue-trdeg)

Proof: By `def-weil-finite-type-morphism`, choose an affine finite type chart Spec A containing
x, with A = K[a₁, …, aₙ], and let p be the prime corresponding to x. The standard opens D(s)
with s outside p form a neighbourhood basis, so taking germs identifies the stalk with Aₚ
(`def-weil-pbc-module-stalk`, `def-weil-pbc-localization-at-prime`). Its maximal ideal consists
of fractions with numerator in p. Reduction a/s ↦ ā/s̄ therefore induces an isomorphism of its
residue field with Frac(A/p) (`def-weil-residue-field`): every denominator lifts outside p,
and the kernel is exactly pAₚ. Hence κ(x) = K(ā₁, …, āₙ). Apply
`lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`, namely
`exists_finset_isTranscendenceBasis`, to obtain a finite transcendence basis B. By
`def-kun-transcendence-degree`, its cardinality is the transcendence degree, which is finite.
The empty basis has cardinality zero, and the empty scheme has no point to check.
-/
theorem finite_trdeg_residueField {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] (x : X) :
    @Algebra.trdeg K (X.residueField x) _ _
      (((X ↘ Spec (CommRingCat.of K)).residueFieldAlgebraMap x).toAlgebra) < Cardinal.aleph0 := by
  sorry

end AlgebraicGeometry
