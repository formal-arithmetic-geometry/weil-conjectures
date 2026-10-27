/-
Copyright (c) 2026 Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
public import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift
import WeilConjectures.AlgebraicGeometry.FiniteRetractSheavesAffineTrivialization
import WeilConjectures.RingTheory.RingPseudoCoherentLocalizationGlue
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison

/-! # Fixed-degree pseudo-coherence under the affine derived equivalence

Source: literature/stacks-project/perfect.tex, Tag 08E7, lemma-pseudo-coherent-affine,
m-pseudo-coherent clause (blueprint: lem-sfb-affine-m-pseudocoherent-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u wA wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For an affine scheme, fixed-degree pseudo-coherence is preserved and reflected by the
termwise associated-sheaf affine derived equivalence, without Noetherian or boundedness
hypotheses.

Source: literature/stacks-project/perfect.tex, Tag 08E7, lemma-pseudo-coherent-affine,
m-pseudo-coherent clause (blueprint: lem-sfb-affine-m-pseudocoherent-criterion).

Proof:
1. Over every commutative ring B, use `new-affine-derived-tilde-homology-comparison`
   to identify cohomology maps naturally with associated-sheaf maps. The fully faithful
   tilde functor preserves cokernels (`lem-weil-pbc-affine-tilde-gamma-adjunction`,
   parts 1, 2, 4), hence preserves and reflects isomorphisms and epimorphisms. It thus
   preserves and reflects the fixed-degree cohomological conditions for arbitrary
   derived morphisms.
2. A bounded finite-free module witness (`def-pc-ring-m-pseudo-coherent`) maps to a
   strictly perfect sheaf witness on the single open Y. Use the affine equivalence
   `lem-pc-affine-qcoh-derived-equivalence`, the structure-sheaf identification from
   `lem-weil-pbc-spec-module-tilde-sections`, and preservation of finite sums in the
   affine tilde/Gamma adjunction. Step 1 gives the cohomological conditions required
   by `def-sfb-m-pseudo-coherent-complex`.
3. Conversely choose a representative N of M. At each point, the sheaf-side predicate
   supplies a strictly perfect approximant P and a derived arrow to tilde N. By
   `def-pc-perfect-complex`, finitely many terms of P can be nonzero, each a retract
   of a finite free sheaf. Apply `lem-pc-finite-retract-sheaves-affine-trivialization`
   to these finitely many terms on a common affine neighbourhood. All other terms
   are already free of rank zero.
4. Refine to principal opens by `lem-weil-pbc-spec-localization-away-basic-open`.
   Restriction is exact by `lem-weil-pbc-module-restriction-open-immersion-limits`
   and `lem-weil-pbc-module-restriction-open-immersion-colimits`. For open immersions,
   `def-pc-derived-pullback` therefore agrees with termwise restriction: restrict a
   K-flat resolution and use exactness to see it remains a quasi-isomorphism.
   This preserves the cohomological conditions, finite free terms and finite degree
   interval. Quasi-compactness gives a finite standard subcover; its elements generate
   the unit ideal by `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.
5. For B = A_f, identify Spec B with D(f) using
   `lem-weil-pbc-principal-localization-open-immersion`. The sections formula and
   restriction maps of `lem-weil-pbc-spec-module-tilde-sections` identify restricted
   tilde N with tilde of the localized N, degree by degree, compatibly with the
   differentials. Thus the resulting comparison is an actual complex isomorphism.
6. Apply `lem-pc-affine-finite-free-sheaf-complex-lift` over each B to obtain a
   bounded-above finite free module complex E whose tilde is the restricted P.
   It is also bounded below: outside P's finite interval, tilde E is zero, hence E
   is zero by the tilde/Gamma unit. Fullness of the affine derived equivalence lifts
   the approximation arrow to a derived module arrow. Step 1 reflects its cohomology
   conditions, giving the ring-side fixed-m witness. No chain-map representative of
   this arrow is needed.
7. Apply the fixed-m clause of `lem-pc-ring-pseudo-coherent-localization-glue` to the
   finite unit-ideal cover. This proves m-pseudo-coherence of M. For the zero ring,
   the spectrum is empty and D(A) is zero: use the empty covering and zero complex.
   Only the approximants were bounded; N was arbitrary and no Noetherian hypothesis
   was used.
-/
theorem affine_mPseudoCoherent_iff (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (m : ℤ) (M : DerivedCategory (ModuleCat.{u} A)) :
    Scheme.IsMPseudoCoherent (Spec (.of A)) m
      ((schemeDerivedQCohProperty (Spec (.of A))).ι.obj
        ((exists_affineQCohDerivedEquivalence.{u, wA, wY} A).choose.functor.obj M)) ↔
      DerivedCategory.IsMPseudoCoherent m M := by
  sorry

end AlgebraicGeometry
