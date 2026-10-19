/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import Sheaf.FieldTheory.AbhyankarInequality
import Sheaf.RingTheory.HeightOneRealAbsoluteValue
import Sheaf.RingTheory.ValuationAlgebraicHeight
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# An etale parameter for a valued smooth function field

Source: Temkin, *Stable modification of relative curves*, Theorem 2.1.8 and its
finite-height proof, printed pp. 10, 12--13; Proposition 4.3.3, printed p. 29
(blueprint: lem-trf-valued-curve-etale-parameter).

The ring `Algebra.adjoin K (W : Set L)` is the subring `KW` of `L`: since `R` has
fraction field `K` and restricts from `W`, adjoining `K` to `W` is precisely
localizing `W` at the nonzero elements of `R`. The generic-point compatibility
is an equality of actual scheme morphisms, using the given field identification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ValuationSubring

/-- A valued smooth function field over a finite-height separably closed valued field
has an integral transcendental parameter inducing an etale extension of valuation rings.
Source: Temkin, Theorem 2.1.8, finite-height proof pp. 12--13, and Proposition 4.3.3,
parameter paragraph p. 29 (blueprint: lem-trf-valued-curve-etale-parameter).

Here `Algebra.adjoin K (W : Set L)` is `(R \ {0})⁻¹W`. The two compatibility
equalities say respectively that the centre is a `K`-morphism and that its generic
restriction is the given identification `e : k(C) ≃+* L`. The function field is
Mathlib's generic stalk, with no substituted model or independent generic map.

Proof plan, following the node's fourteen steps:
1. Induct on the finite height of `R`, initially allowing a parameter outside `W`.
   Use lem-trf-curve-separating-parameters for separating parameters and their proper
   bad-parameter subfield. Use lem-trf-valuation-height-coarsening and
   lem-trf-valuation-algebraic-height for finite heights of the valuations involved.
2. An etale algebra over a valuation ring with finitely many primes has finite spectrum,
   by lem-weil-pbc-etale-scheme-base-change and
   lem-weil-pbc-etale-algebra-over-field-product. For a prime `q`, take a product of
   elements in each prime not contained in `q`, but outside `q`. Its principal open
   is exactly the primes below `q`, and realizes localization at `q`. Thus that
   localization is etale by lem-weil-pbc-etale-composition-cancellation.
3. When `KW` is not `L`, lem-trf-curve-centred-valuation-dvr gives a genuine etale
   coordinate and a local extension of DVRs with equal residue fields; step 2
   upgrades the essentially etale extension to an etale one.
4. By lem-trf-valuation-height-coarsening, `W` and its restriction to the rational
   subfield are inverse images of the same residual valuation. Apply
   lem-trf-composed-valuation-etale with the identity residual map.
5. If `KW = L` and the base height is zero, both valuation rings are fields; a
   separating parameter works by lem-weil-pbc-finite-separable-extension-etale.
6. At positive height use lem-trf-valuation-height-coarsening to form compatible
   height-one coarsenings and residual valuations with smaller base height.
   Lemmas lem-trf-height-one-real-absolute-value and lem-trf-sepclosed-rank-one-completion
   supply real absolute values, algebraically closed completion and residue field.
7. The complement of the proper bad-parameter `K`-subspace is dense: if `b` is
   outside it and `0 < |c| < 1` with `c` in `K`, the points `d + b*c^n` approach
   any point `d` in the subspace while staying outside it. Also use density in the completion.
8. A separating parameter makes `L` finite over its rational subfield. By
   lem-trf-valued-decompletion-etale its completion is finite over the completed
   rational field, which is the closure of the rational field over the base completion.
9. If the residual extension is trivial, use lem-trf-analytic-uniformization and
   step 7 to choose a separating parameter with etale completed valuation extension.
   If the completions already agree, any separating parameter works. Apply
   lem-trf-valued-decompletion-etale, then lem-trf-composed-valuation-etale with
   the identity residual valuation map.
10. Otherwise lem-trf-abhyankar-inequality gives residual transcendence degree one.
    A lift of a transcendental residue has rational residue field by the Gauss
    calculation. Residue-linear independence lifts to linear independence in `L`,
    bounding the residual degree by the finite rational degree; thus it is finite.
11. Lemma lem-trf-algclosed-curve-model supplies a smooth proper residual curve and
    a centre. Induction gives a residual parameter. Its finite residual extension
    is separable, by base change of the etale valuation-ring map to fraction fields
    and lem-weil-pbc-etale-algebra-over-field-product.
12. Lift that parameter within its open residue ball, using step 7 to make it
    separating. The residue-prescribed clause of lem-trf-analytic-uniformization
    and lem-trf-valued-decompletion-etale give an etale height-one extension.
13. Restriction commutes with inverse images by lem-trf-valuation-height-coarsening.
    Combine the height-one and residual etale maps using lem-trf-composed-valuation-etale.
14. Replace the nonzero transcendental parameter by its inverse if it is outside `W`.
    The valuation alternative puts the inverse in `W`, and the rational subfield,
    finiteness and etale inclusion are unchanged. -/
theorem exists_etale_parameter_of_smooth_centre
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosed K]
    (R : ValuationSubring K) [Finite (PrimeSpectrum R)]
    (W : ValuationSubring L) (hrestrict : W.comap (algebraMap K L) = R)
    (hfg : (⊤ : IntermediateField K L).FG) (htrdeg : Algebra.trdeg K L = 1)
    (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of K))]
    [Smooth (C ↘ Spec (.of K))] [LocallyOfFiniteType (C ↘ Spec (.of K))]
    [QuasiCompact (C ↘ Spec (.of K))] (hdim : topologicalKrullDim C = 1)
    (e : C.functionField ≃+* L)
    (centre : Spec (.of (Algebra.adjoin K (W : Set L))) ⟶ C)
    (hcentre : centre ≫ (C ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Algebra.adjoin K (W : Set L)))))
    (hgeneric :
      Spec.map (CommRingCat.ofHom (Algebra.adjoin K (W : Set L)).val.toRingHom) ≫ centre =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk (genericPoint C)) :
    ∃ t : L, t ∈ W ∧ Transcendental K t ∧
      Module.Finite (IntermediateField.adjoin K {t}) L ∧
      Etale (Spec.map (CommRingCat.ofHom
        (W.comapInclusion (algebraMap (IntermediateField.adjoin K {t}) L)))) := by
  sorry

end ValuationSubring
