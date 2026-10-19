/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Completed lattice monoids and supported power series

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70, for the
completed monoid models; the comparison and projection are the agent-formulated
auxiliary algebra in the DAG (blueprint: lem-trf-completed-monoid-support-projection).
-/

@[expose] public section

universe u

namespace AddMonoidAlgebra

open Classical in
/-- The completion of a lattice monoid algebra is the supported part of the ambient
power series ring, with its coefficient projection and module retraction.

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70, specifies the
completed monoid models. This comparison is auxiliary agent algebra, with the full
coefficient argument in the DAG (blueprint: lem-trf-completed-monoid-support-projection).

Here `hQ`, `hJ` and `hI` name precisely the monoid and ideals in the node, rather than
introducing additional choices. The infimum of the topologies induced by the maps to
the discrete quotients is the inverse-limit topology of the completion. The identities
for `ρ` express linearity for the action of the completion on series through `ι`;
`ι (ρ b) = π b` identifies `ρ` with the inverse of `ι` on its image followed by `π`.

Proof: (1) Send the monoid basis to the corresponding power series monomials. Distinct
exponents give distinct coefficients, so this algebra map is injective. Apply
`power_series_mem_combined_ideal_pow_iff` to detect powers of `I` by coefficients.
(2) Choose nonzero monoid generators and bound their total degrees by `D ≥ 1`.
For the pulled-back filtration `E n`, one has `J^n ≤ E n` and `E (D*n) ≤ J^n`:
write an exponent with `h` generator factors. If `h ≥ n` its monomial is in `J^n`;
otherwise its coefficient is in `m^(D*n-|q|)`, with `D*n-|q| ≥ n-h`.
(3) Representatives of a compatible family differ by `J^n`. For each exponent `e`,
their coefficients stabilize modulo `m^k` for `n ≥ k+|e|`. Completeness of `L` gives
a unique coefficient limit, independent of representatives, and hence a series `ι x`.
(4) Finite coefficient convolution proves multiplicativity; addition, constants and
the basis extension follow similarly. Separatedness follows from injectivity of the
completion map of `L`. (5) If `ι x = 0`, use a representative at level `D*n` and the
reverse filtration estimate to show `x n = 0`, so `ι` is injective.
(6) All coefficients outside `Q` vanish. Conversely, truncate a supported series below
degree `D*n`; the resulting polynomials are compatible modulo `J^n`, giving a preimage.
(7) The kernel of evaluation at level `n` maps into `I^n`, proving continuity.
Polynomial representatives converge to each compatible family; the target is separated
by the coefficient criterion, so a continuous extension is unique.
(8) Define `π` by retaining coefficients in `Q`. It is additive and fixes supported
series. For `a` supported in `Q`, the coefficient convolution proves `π (a*b)=a*π b`:
if `u,q ∈ Q` and `q+e=u`, the subgroup condition gives `e ∈ Q`; if `u ∉ Q`, a term
with both factors in `Q` cannot occur. (9) Transport `π` through the bijection from
the completion to the supported series. The preceding multiplication identity proves
the displayed linearity law for `ρ`, and fixing the image gives `ρ (ι t)=t`.
The empty generator list uses `D=1`; all steps include rank zero and `Q={0}`. -/
theorem exists_completedMonoid_supportProjection
    (r : ℕ) (M : AddSubgroup (Fin r → ℤ)) (Q : AddSubmonoid (Fin r →₀ ℕ))
    (hQ : ∀ e : Fin r →₀ ℕ, e ∈ Q ↔ (fun i : Fin r ↦ (e i : ℤ)) ∈ M)
    (hfg : Q.FG) (L : Type u) [CommRing L] [IsLocalRing L]
    (hmfg : (IsLocalRing.maximalIdeal L).FG)
    (hcomplete : Function.Bijective (AdicCompletion.of (IsLocalRing.maximalIdeal L) L))
    (J : Ideal (AddMonoidAlgebra L Q))
    (hJ : J = Ideal.map (algebraMap L (AddMonoidAlgebra L Q))
        (IsLocalRing.maximalIdeal L) ⊔
      Ideal.span {b | ∃ q : Q, q ≠ 0 ∧ b = single q (1 : L)})
    (I : Ideal (MvPowerSeries (Fin r) L))
    (hI : I = Ideal.map (algebraMap L (MvPowerSeries (Fin r) L))
        (IsLocalRing.maximalIdeal L) ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) L))) :
    ∃ ι : AdicCompletion J (AddMonoidAlgebra L Q) →ₐ[L] MvPowerSeries (Fin r) L,
      (∀ (q : Q) (c : L),
        ι (AdicCompletion.of J (AddMonoidAlgebra L Q) (single q c)) =
          MvPowerSeries.monomial q.val c) ∧
      @Continuous _ _
        (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ J n) ⊥)
        I.adicTopology ι ∧
      Function.Injective ι ∧
      (∀ F : MvPowerSeries (Fin r) L,
        (∃ t : AdicCompletion J (AddMonoidAlgebra L Q), ι t = F) ↔
          ∀ e : Fin r →₀ ℕ, e ∉ Q → MvPowerSeries.coeff e F = 0) ∧
      (∀ κ : AdicCompletion J (AddMonoidAlgebra L Q) →ₐ[L] MvPowerSeries (Fin r) L,
        @Continuous _ _
          (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ J n) ⊥)
          I.adicTopology κ →
        (∀ (q : Q) (c : L),
          κ (AdicCompletion.of J (AddMonoidAlgebra L Q) (single q c)) =
            MvPowerSeries.monomial q.val c) → κ = ι) ∧
      ∃ π : MvPowerSeries (Fin r) L →+ MvPowerSeries (Fin r) L,
        (∀ (F : MvPowerSeries (Fin r) L) (e : Fin r →₀ ℕ),
          MvPowerSeries.coeff e (π F) = if e ∈ Q then MvPowerSeries.coeff e F else 0) ∧
        (∀ F : MvPowerSeries (Fin r) L,
          (∀ e : Fin r →₀ ℕ, e ∉ Q → MvPowerSeries.coeff e F = 0) → π F = F) ∧
        (∀ a b : MvPowerSeries (Fin r) L,
          (∀ e : Fin r →₀ ℕ, e ∉ Q → MvPowerSeries.coeff e a = 0) →
            π (a * b) = a * π b) ∧
        ∃ ρ : MvPowerSeries (Fin r) L →+ AdicCompletion J (AddMonoidAlgebra L Q),
          (∀ b : MvPowerSeries (Fin r) L, ι (ρ b) = π b) ∧
          (∀ (t : AdicCompletion J (AddMonoidAlgebra L Q)) (b : MvPowerSeries (Fin r) L),
            ρ (ι t * b) = t * ρ b) ∧
          ∀ t : AdicCompletion J (AddMonoidAlgebra L Q), ρ (ι t) = t := by
  sorry

end AddMonoidAlgebra
