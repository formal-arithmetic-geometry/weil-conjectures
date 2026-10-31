/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude

/-!
# Finite-coefficient condensed projection formula

Source: blueprint slopmaster2-20261029-2300,
`sec-six-functors-basics/sk-thm-sf-pf-adic/det-thm-sf-pf-finite.md`, node
det-thm-sf-pf-finite, order 2765; proof in the latest blueprint's
`det-thm-sf-pf-finite.proof.md` (blueprint: det-thm-sf-pf-finite).

This is the condensed-module projection-formula statement attached to
`det-thm-sf-pf-finite`.  The ordinary condensed-module `PF` of `det-def-sf-exchanges` is
the `CompactificationReindexing.pf` component `Rp_*(γ) ∘ π`.  Étale complexes are
transported by the canonical site comparison `ν^*` and by the canonical finite
coefficient equivalence whose scalar map is `constRingSheafToCondensedRingObj`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical condensed coefficient realization of the bounded-below site pullback.
It is the composition of `ν^* = siteComparisonDerivedPullbackPlus`, the inclusion of
bounded-below derived categories, and the inverse of the finite coefficient equivalence.
The latter is induced by the canonical constant-scalar map
`constRingSheafToCondensedRingObj`, so this is not an arbitrary choice of transport.
Source: blueprint node det-thm-sf-pf-finite, order 2765, proof step "Étale-to-condensed
realization of the specified PF component" (`ν^*K`, `ν^*L` at `Λ = A_{E,n}`)
(blueprint: det-thm-sf-pf-finite). -/
noncomputable def condensedSiteComparisonDerivedPullbackPlus
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] (X : Scheme.{u})
    (K : AlgebraicGeometry.Etale.DerivedCategoryModule
      (ULift.{u + 1} T) X)
    (hK : DerivedCategory.TStructure.t.plus K) :=
  (finiteCoefficientDerivedEquivalence X T).inverse.obj
    ((siteComparisonDerivedPullbackPlus X (ULift.{u + 1} T)).obj ⟨K, hK⟩).obj

/-- Bounded constructibility supplies the lower bound needed to use the canonical
`siteComparisonDerivedPullbackPlus` functor.
Proof: the second clause of `isBoundedConstructible` gives `a ≤ b` with
`H^i K = 0` for `i ∉ [a, b]`; in particular `H^i K = 0` for `i < a`, so `K` lies in
`D^{≥ a}` by `DerivedCategory.isGE_iff`, hence in the `plus` part of the standard
t-structure.
Source: blueprint node det-thm-sf-pf-finite, order 2765, proof step "Naturality and
bounded-below target" (bounded `K` is bounded below) (blueprint: det-thm-sf-pf-finite). -/
theorem boundedConstructible_plus
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (K : AlgebraicGeometry.Etale.DerivedCategoryModule Λ X)
    (hK : AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible Λ X K) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, b, _, hv⟩ := hK.2
  exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).2
    (fun q hq ↦ hv q (Or.inl hq))⟩

/-- Finite-coefficient condensed projection formula for the specified compactification.
Source: blueprint slopmaster2-20261029-2300, node det-thm-sf-pf-finite, order 2765
(blueprint: det-thm-sf-pf-finite).
The component is the condensed-module `CompactificationReindexing.pf`, evaluated at the
canonical finite coefficient realizations of `ν^* K` and `ν^* L`.

Proof (deferred), following the node's steps:
1. `X`, `Y` are qcqs, so the compactification `c = (j, p)` of `f` exists (Nagata) and is
   fixed; the étale projection component `PF^{et,c}_{f,K,L}` is the proper counit-defined
   projection for `p` at `(j_!K, L)` followed by `Rp_*` of the open tensor comparison
   (def-kun-projection-formula-map, lem-pur-etale-open-derived-tensor).
2. `Λ = A_{E,n}` is finite; the proper projection formula
   (lem-etale-proper-projection-formula-finite) makes the proper factor an isomorphism
   for all `j_!K`, `L`, and the open comparison is an isomorphism, so `PF^{et,c}` is an
   isomorphism natural in `K`, `L`; no finite-field hypothesis is used.
3. Source and target are bounded below: `j_!` is exact, `Rp_*` keeps the lower bound,
   and finite Tor amplitude of `L` bounds the tensor products below.
4. The étale-to-condensed comparison
   (new-lem-det-sf-pf-finite-etale-condensed-comparison) gives
   `C ∘ PF^p_{ν^*K,ν^*L} = ν^*(PF^{et,c}_{f,K,L}) ∘ t ∘ (C_K ⊗ 1)`, with `C` the
   compact-support site comparison, `t` the tensor comparison and
   `PF^p = Rp_*(γ) ∘ π = CompactificationReindexing.pf` (det-def-sf-exchanges).
5. `C_K ⊗ 1`, `t`, `C` are isomorphisms and `ν^*(PF^{et,c})` is one by step 2, hence
   `pf` is an isomorphism; naturality follows from the naturality of all maps in step 4. -/
theorem det_finite_condensed_projection_formula
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    let A := Padic.coefficientExtensionRing l E n
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
    letI : Finite A := Padic.finite_coefficientExtensionRing l E n hn
    ∀ (K : AlgebraicGeometry.Etale.DerivedCategoryModule (ULift.{u + 1} A) X)
      (L : AlgebraicGeometry.Etale.DerivedCategoryModule (ULift.{u + 1} A) Y),
      (_hK : AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1} A) X K) →
      (_hL : AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1} A) Y L) →
      (_hLt : ∃ a b : ℤ,
        AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn
          (ULift.{u + 1} A) Y a b L) →
      IsIso
        (CondensedRing.CompactificationReindexing.pf
          (Profinite.continuousMapRingObj A) c
          ((condensedSiteComparisonDerivedPullbackPlus A X K
            (boundedConstructible_plus (ULift.{u + 1} A) X K _hK)))
          ((condensedSiteComparisonDerivedPullbackPlus A Y L
            (boundedConstructible_plus (ULift.{u + 1} A) Y L _hL)))) := by
  sorry

end AlgebraicGeometry.ProEtale
