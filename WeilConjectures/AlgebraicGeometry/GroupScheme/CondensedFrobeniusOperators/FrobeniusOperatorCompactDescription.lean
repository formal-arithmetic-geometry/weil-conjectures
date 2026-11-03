/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaIteratedWeil
import WeilConjectures.AlgebraicGeometry.GroupScheme.CompactWeilCocycleEndomorphismRecurrence

/-!
# Compact-support description of the global Frobenius

Source: latest blueprint, `lem-trf-frobenius-operator-compact-description`,
node order 2298 (blueprint: lem-trf-frobenius-operator-compact-description).

The direct compact-support transport is the canonical finite coefficient transport for the
powered geometric-Frobenius square.  The theorem records both its explicit compact-support
composite and its identification with the corresponding power of the degree-one operator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators

open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The direct compact-support base-change arrow for the `m`-th geometric Frobenius power.
Source: latest blueprint, `lem-trf-frobenius-operator-compact-description`, node order 2298
(blueprint: lem-trf-frobenius-operator-compact-description).

It is formed from the canonical finite transport datum and the powered geometry, so its
underlying arrow is point insertion followed by the retained compactification exchange.
-/
noncomputable def finiteGlobalDirectPowerTransport
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (c : Compactification (condensedFrobeniusGeometry F Y₀).a) (m : ℕ) (_hm : 1 ≤ m) :=
  let Λ := finiteCoefficient ell E n
  let q := poweredGeometry F Y₀ m
  let S := finiteTransportData F ell hEll E n hn
  let hM := S.property.pull_constructible q K.carrier
  compactTransport Λ S.val q c c K.carrier hM

/-- The `m`-th compactly supported Frobenius is its direct compact-support composite and the
`m`-th power of the degree-one operator.
Source: latest blueprint, `lem-trf-frobenius-operator-compact-description`, node order 2298
(blueprint: lem-trf-frobenius-operator-compact-description).

Proof plan: unfold the finite global operator and apply the canonical direct-power transport
normalization to obtain the displayed compact-support composite.  The transport composition
law and the iterated Weil cocycle identify the resulting operator with the power of the
degree-one operator; induction on the positive exponent starts at one and uses the successor
power identity.  The positivity hypothesis supplies the finite coefficient level and excludes
an undefined zero-level convention.
-/
theorem frobenius_operator_compact_description
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (c : Compactification (condensedFrobeniusGeometry F Y₀).a)
    (m : ℕ) (hm : 1 ≤ m) :
    condensedGlobalFrobenius F Y₀ ell hEll E n hn K c m hm =
        (condensedGlobalFrobenius F Y₀ ell hEll E n hn K c 1 (Nat.le_refl 1)) ^ m ∧
      condensedGlobalFrobenius F Y₀ ell hEll E n hn K c m hm =
        finiteGlobalDirectPowerTransport F Y₀ ell hEll E n hn K c m hm ≫
          (Γ (finiteCoefficient ell E n) (Spec (.of F.k))).map
            ((C (finiteCoefficient ell E n) c).map
              (iteratedWeil F Y₀ ell E n hn K m).hom) ∧
      IsIso (finiteGlobalDirectPowerTransport F Y₀ ell hEll E n hn K c m hm) := by
  refine ⟨?_, rfl, ?_⟩
  · induction m with
    | zero => omega
    | succ r ih =>
      by_cases hz : r = 0
      · subst r
        exact (pow_one _).symm
      · have hr : 1 ≤ r := by omega
        rw [(compact_weil_cocycle_endomorphism_recurrence
          F Y₀ ell hEll E n hn K c).2 r hr, ih hr, pow_succ']
        rfl
  · exact ((finiteTransportData F ell hEll E n hn).property.transport_iso
      (poweredGeometry F Y₀ m) c c K.carrier).2

end WeilConjectures.CondensedFrobeniusOperators
