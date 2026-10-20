/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Sheaf.Paper.PbcQbarStandardCohomology
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.PbcSupportCondition
public import Sheaf.Paper.AdicHeartPullbackFibres
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.DeligneLaumon.ConstructibleSubsetClosureDimension
import Sheaf.AlgebraicGeometry.SmoothLocalDimension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
import Mathlib.Topology.KrullDimension
import Sheaf.Paper.AdicHeartIntrinsicFibres
import Sheaf.Paper.QbarPerverseSupportCondition
import Sheaf.Paper.SfCommonStageWeilCohomology

/-! # Smooth pullback cohomology and support dimension

Source: Stacks Tag 0AFF, lemma-smoothness-dimension; blueprint main-20261015,
sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.proof.md,
first paragraph (blueprint: lem-per-smooth-pullback-support-dimension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Smooth shifted pullback commutes naturally with standard cohomology and increases
cohomology support dimension by at most the constant relative dimension. Cohomology
objects are viewed in the standard heart inside the same Qbar category. Pullback
preserves both standard bounds, so its restriction there is the exact sheaf pullback.

Source: Stacks 0AFF; blueprint smooth-pullback proof, first paragraph
(blueprint: lem-per-smooth-pullback-support-dimension).

Proof:
1. The adic heart pullback and fibre calculation of lem-per-adic-heart-pullback-fibres
makes degree-zero pullback exact. Bounded truncation devissage, using extension
closure and long exact cohomology sequences of lem-weil-heart-short-exact-triangles,
shows that pullback preserves both standard bounds. Uniqueness of truncation
triangles with identity on the middle term gives the canonical natural comparisons
with both truncations and hence with each cohomology object. These are the rational
images of the ambient cohomology sheaves, compatibly with finite scalar extension.
The argument only needs invertibility on the schemes. In characteristic l these
hypotheses force both schemes to be empty, where every assertion is immediate.
2. For cohomological shifts, the degree-n term of C[d] is C^(n+d), with differential
multiplied by a sign. Kernels and images are unchanged by that sign, so
H^n(C[d]) is canonically H^(n+d)(C). Set n = -i and compose with Step 1.
3. The geometric fibre calculation identifies the nonzero-fibre locus of pullback
with the inverse image of the original constructible locus S. Support as recorded
in def-per-support-condition is its closure. Empty support has dimension bottom,
and bottom plus the finite d is bottom, so the empty case is included.
4. Give the closure of S its reduced induced closed scheme structure Z. Base change
f to W = X times_Y Z. Smoothness and relative dimension d survive base change.
The other projection embeds W as the closed inverse image of the closure of S.
Both W and Z are finite type over k and therefore noetherian.
5. Stacks 0AFF, lem-per-smooth-local-dimension and the supremum of local dimensions
give dim W <= dim Z + d, also when W is empty. No surjectivity of f is required.
6. Monotonicity of dimension bounds dim(f inverse S) by dim W. The constructible
subset closure lemma identifies dim Z with dim S, and likewise identifies the
dimension of the constructible inverse image with that of its closure. Combine
these bounds with Step 2 to obtain the displayed inequality for every i. -/
theorem pbcSmoothPullbackSupportDimension
    {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X Y : PerAdic.Base k)
    [iX : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [iY : Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    (f : X.scheme ⟶ Y.scheme) (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∀ (n : ℤ) (K : pbcQbarCategory l Ω Y.scheme),
      ((pbcQbarStandardT l Ω Y.scheme).le n K →
        (pbcQbarStandardT l Ω X.scheme).le n ((pbcQbarCompletedPull l Ω f).obj K)) ∧
      ((pbcQbarStandardT l Ω Y.scheme).ge n K →
        (pbcQbarStandardT l Ω X.scheme).ge n ((pbcQbarCompletedPull l Ω f).obj K))) ∧
    (∀ i : ℤ, Nonempty
      (pbcQbarCompletedPull l Ω f ⋙ shiftFunctor (pbcQbarCategory l Ω X.scheme) (d : ℤ) ⋙
          pbcQbarCohomology l Ω X.scheme (-i) ≅
        pbcQbarCohomology l Ω Y.scheme (-i + (d : ℤ)) ⋙ pbcQbarCompletedPull l Ω f)) ∧
    (∀ (K : pbcQbarCategory l Ω Y.scheme) (i : ℤ),
      topologicalKrullDim (pbcQbarCohomologySupport l Ω X.scheme
        ((shiftFunctor (pbcQbarCategory l Ω X.scheme) (d : ℤ)).obj
          ((pbcQbarCompletedPull l Ω f).obj K)) (-i)) ≤
      topologicalKrullDim
        (pbcQbarCohomologySupport l Ω Y.scheme K (-i + (d : ℤ))) +
          (d : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry.Scheme
