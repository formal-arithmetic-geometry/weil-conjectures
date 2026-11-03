/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFieldCompactScalarSiteSquare
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility2
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# Existence of the normalized finite-ctf summation realization

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts.
(blueprint: lem-pur-general-field-etale-sum-realization-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Transport ordinary summation and evaluation to the intrinsic finite-ctf categories.
Source: latest blueprint, exceptional-reduction proof, Charts, finite-site transport
(blueprint: lem-pur-general-field-etale-sum-realization-existence).

Proof: restrict ordinary summation to the finite-ctf domain using the compact-support
normalization and compact-support preservation. Ordinary pullback preserves this domain.
Conjugate the restricted sum/evaluation adjunction by the finite-site equivalences and
identify its right functor with the actual intrinsic pullback by reductionSitePullbackIso.
Take the left comparison on origins to be the proper/open site comparison followed by
the canonical graph normalization. Extend it uniquely through the source equivalence.
The transported counit formula is the counit of the conjugated adjunction; naturality
and the equivalence triangle identities give the displayed normalization fields.
This constructs all data explicitly before asserting its existence. Empty sums remain
zero, and infinite sheet sums use finite-support sections. -/
theorem generalFieldEtaleSumRealization_exists
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {U V : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (e : U ⟶ V) [e.IsOver (Spec (.of k))]
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e)
    [IsNoetherian U] [IsNoetherian V]
    (R : Type u) [CommRing R] [Finite R]
    (n : ℕ) (hn : 1 ≤ n) (hR : ((ell ^ n : ℕ) : R) = 0)
    (hF : ∀ M : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor V R ((reductionCompactSupport R c.i c.g).obj M.obj)) :
    Nonempty (GeneralFieldEtaleSumRealization R e c hF) := by
  sorry

end AlgebraicGeometry.ProEtale
