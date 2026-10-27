module

public import Sheaf.RingTheory.ContinuousKaehlerDifferential
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.SixFunctors.TraceFormula.FormalPowerSeriesContinuousFree
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.FiniteModuleComplete

/-! # Complete relation quotient of continuous differentials

Source: Stacks Project, algebra.tex, Tags 00RU, 00RO, 0306 and 00MA (3),
continuous conormal auxiliary construction
(blueprint: lem-trf-formal-conormal-quotient-data).

The tensor factors follow the recorded base-change convention `R ⊗[D] M`.
Truncation index `r : ℕ` denotes the positive exponent `r + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

universe u

namespace RingTheory.FormalConormal

variable (F : Type u) [Field F] (n : ℕ)

/-- The ideal of variables. Source: Stacks, algebra.tex, Tag 0306
(blueprint: lem-trf-formal-conormal-quotient-data). -/
def variablesIdeal : Ideal (MvPowerSeries (Fin n) F) :=
  Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F))

variable {F n} {s : ℕ} (f : Fin s → MvPowerSeries (Fin n) F)

/-- The ideal of the specified relations. Source: Stacks, algebra.tex, Tag 00RU
(blueprint: lem-trf-formal-conormal-quotient-data). -/
def relationIdeal : Ideal (MvPowerSeries (Fin n) F) := Ideal.span (Set.range f)

/-- The quotient ring by the relations. Source: Stacks, algebra.tex, Tag 00RU
(blueprint: lem-trf-formal-conormal-quotient-data). -/
abbrev Ring := MvPowerSeries (Fin n) F ⧸ relationIdeal f

/-- The image of the variable ideal in the quotient. Source: Stacks, algebra.tex, Tag 00MA
(blueprint: lem-trf-formal-conormal-quotient-data). -/
def maximalIdeal : Ideal (Ring f) :=
  (variablesIdeal F n).map (Ideal.Quotient.mk (relationIdeal f))

/-- The continuous differential module before imposing relations.
Source: Stacks, algebra.tex, Tags 00RO and 00RU
(blueprint: lem-trf-formal-conormal-quotient-data). -/
abbrev Differentials (F : Type u) [Field F] (n : ℕ) :=
  KaehlerDifferential.Continuous F (MvPowerSeries (Fin n) F) (variablesIdeal F n)

/-- Extension of scalars of continuous differentials to the quotient ring.
Source: Stacks, algebra.tex, Tag 00RU
(blueprint: lem-trf-formal-conormal-quotient-data). -/
abbrev TensorModule := Ring f ⊗[MvPowerSeries (Fin n) F] Differentials F n

/-- The span of the relation differentials in the base-changed module.
Source: Stacks, algebra.tex, Tag 00RU
(blueprint: lem-trf-formal-conormal-quotient-data). -/
def relations : Submodule (Ring f) (TensorModule f) :=
  Submodule.span (Ring f) (Set.range fun j : Fin s ↦
    (1 : Ring f) ⊗ₜ[MvPowerSeries (Fin n) F]
      KaehlerDifferential.continuousD F (MvPowerSeries (Fin n) F)
        (variablesIdeal F n) (f j))

/-- The relation quotient `N = T/L`. Source: Stacks, algebra.tex, Tag 00RU
(blueprint: lem-trf-formal-conormal-quotient-data). -/
abbrev QuotientModule := TensorModule f ⧸ relations f

/-- The positive adic quotient of the relation ring. Source: Stacks, algebra.tex, Tag 00MA
(blueprint: lem-trf-formal-conormal-quotient-data). -/
abbrev Truncation (r : ℕ) := Ring f ⧸ maximalIdeal f ^ (r + 1)

/-- The complete relation quotient, its descended derivation, and its compatible maps to
truncated Kähler differentials. Source: Stacks, algebra.tex, Tags 00RU, 00RO, 0306, 00MA (3)
(blueprint: lem-trf-formal-conormal-quotient-data).

Proof:
1. The coordinate basis of `lem-trf-formal-power-series-continuous-free` generates the
   tensor module after base change, and its images generate the quotient. Coefficients in
   the relation ring lift to the power-series ring, giving finite generation over that ring.
2. The power-series ring is Noetherian (Tag 0306) and complete for the variable ideal.
   Apply `lem-weil-pbc-finite-module-complete-over-complete-noetherian` (Tag 00MA (3)).
   The image of the r-th power of the variable ideal is the r-th power of its image;
   lifting coefficients proves equality of the two power submodules. Thus the canonical
   completion map for the image ideal is bijective, hence an R-linear isomorphism.
3. Compose the continuous derivation with base change and the quotient map. Leibniz gives
   zero on every sum of multiples of the relations: their coefficients vanish in R and
   their differentials vanish modulo L. It therefore descends to an F-derivation on R
   with the asserted formula (Tag 00RU).
4. The quotient ring map at each positive adic level induces the differential map u by
   the universal property (Tag 00RO). Composing with the continuous coordinate projection
   gives a D-linear map whose scalar action factors through R. Tensor balancing extends
   it to T. It kills each relation differential since each relation is zero in R_r,
   and hence descends through L to the asserted R-linear map phi (Tag 00RU).
5. On any lift of x in R the defining formulas give phi(delta(x)) = d(x mod m^r).
   Both adjacent transition composites are R-linear and agree on the coordinate
   differential generators, so they agree everywhere (Tag 00RO). -/
theorem quotientData (hf : ∀ j : Fin s, f j ∈ variablesIdeal F n) :
    Module.Finite (MvPowerSeries (Fin n) F) (QuotientModule f) ∧
    Submodule.span (Ring f) (Set.range fun i : Fin n ↦
      (relations f).mkQ ((1 : Ring f) ⊗ₜ[MvPowerSeries (Fin n) F]
        KaehlerDifferential.continuousD F (MvPowerSeries (Fin n) F)
          (variablesIdeal F n) (MvPowerSeries.X i))) = ⊤ ∧
    Function.Bijective (AdicCompletion.of (maximalIdeal f) (QuotientModule f)) ∧
    (∀ r : ℕ,
      (variablesIdeal F n ^ (r + 1) • (⊤ : Submodule (MvPowerSeries (Fin n) F)
        (QuotientModule f))) =
      (maximalIdeal f ^ (r + 1) • (⊤ : Submodule (Ring f) (QuotientModule f))).restrictScalars
        (MvPowerSeries (Fin n) F)) ∧
    ∃ u : ∀ r : ℕ,
        KaehlerDifferential F (MvPowerSeries (Fin n) F ⧸ variablesIdeal F n ^ (r + 1))
          →ₗ[MvPowerSeries (Fin n) F] KaehlerDifferential F (Truncation f r),
      (∀ (r : ℕ) (h : MvPowerSeries (Fin n) F),
        u r (KaehlerDifferential.D F _
          (Ideal.Quotient.mk (variablesIdeal F n ^ (r + 1)) h)) =
        KaehlerDifferential.D F (Truncation f r)
          (Ideal.Quotient.mk (maximalIdeal f ^ (r + 1))
            (Ideal.Quotient.mk (relationIdeal f) h))) ∧
      ∃ (δ : Derivation F (Ring f) (QuotientModule f))
        (φ : ∀ r : ℕ, QuotientModule f →ₗ[Ring f]
          KaehlerDifferential F (Truncation f r)),
        (∀ h : MvPowerSeries (Fin n) F,
          δ (Ideal.Quotient.mk (relationIdeal f) h) =
          (relations f).mkQ ((1 : Ring f) ⊗ₜ[MvPowerSeries (Fin n) F]
            KaehlerDifferential.continuousD F (MvPowerSeries (Fin n) F)
              (variablesIdeal F n) h)) ∧
        (∀ (r : ℕ) (m : Differentials F n) (a : Ring f),
          φ r ((relations f).mkQ (a ⊗ₜ[MvPowerSeries (Fin n) F] m)) =
            a • u r (m.val r)) ∧
        (∀ (r : ℕ) (x : Ring f), φ r (δ x) =
          KaehlerDifferential.D F (Truncation f r)
            (Ideal.Quotient.mk (maximalIdeal f ^ (r + 1)) x)) ∧
        (∀ (r : ℕ) (z : QuotientModule f),
          KaehlerDifferential.adicTransition F (Ring f) (maximalIdeal f) r
            (φ (r + 1) z) = φ r z) := by
  sorry

end RingTheory.FormalConormal
