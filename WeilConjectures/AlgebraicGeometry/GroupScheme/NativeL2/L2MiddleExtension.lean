/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2PureWeight
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleEnergyBound
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2EnergyComparison
public import WeilConjectures.AlgebraicGeometry.AffineSpace.GeometricallyConnected

/-!
# Middle extension preserves the L² weight

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-l2-middle/
lem-fd-l2-middle-extension.md (blueprint: lem-fd-l2-middle-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

/-- The affine-line model inherits the existing finite-type structural-map instance.
This only exposes the definitional Over.mk projection to instance search.
Source: Mathlib AffineSpace finite-presentation instance
(blueprint: lem-fd-l2-middle-extension). -/
local instance affineLineModel_locallyOfFiniteType (D : FiniteFieldDatum.{u}) :
    LocallyOfFiniteType (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (affineLine D.k₀ ↘ Spec (.of D.k₀)))

/-- The same model inherits quasi-compactness of the existing affine-space morphism.
Source: Mathlib AffineSpace isAffineHom instance
(blueprint: lem-fd-l2-middle-extension). -/
local instance affineLineModel_quasiCompact (D : FiniteFieldDatum.{u}) :
    QuasiCompact (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))).hom :=
  inferInstanceAs (QuasiCompact (affineLine D.k₀ ↘ Spec (.of D.k₀)))

/-- A nonzero punctually pure lisse Weil sheaf on a dense open of the affine line
has the same L² weight as its ordinary middle extension, and both equal its weight.

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-l2-middle/
lem-fd-l2-middle-extension.md (blueprint: lem-fd-l2-middle-extension).

Proof: purity rigidity on the smooth geometrically connected affine open gives ||M||=w.
The canonical restriction identification gives equality of traces on U₀(k_m), hence
S_m(j_*M)=S_m(M)+E_m with E_m nonnegative. The boundary is finite; its point count is
bounded by D=sum_s d(s). The invariant-stalk description bounds each boundary dimension
by the lisse rank r. Boundary semicontinuity bounds the squared absolute eigenvalues
by q_s^w. Local Frobenius powers therefore bound each boundary squared trace by
r² q^(mw), so E_m ≤ D r² q^(mw). Nonnegativity gives ||j_*M|| ≥ ||M||. For β>w,
the normalized original energy has limsup zero; the additional normalized contribution
is bounded by D r² q^(m(w-β-1)), which tends to zero. Thus ||j_*M|| ≤ w.
-/
theorem l2Weight_middleExtension
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (iota : PadicAlgCl l →+* ℂ)
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀)))
    [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (_hlisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (_hne : ¬ IsZero M) (w : ℝ) (_hpure : Pure D l U₀ M iota w) :
    l2Weight D l (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))) iota
        (middleWeilImage D l j₀ M) = l2Weight D l U₀ iota M ∧
      l2Weight D l U₀ iota M = (w : EReal) := by
  let C₀ := Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))
  have hpure : l2Weight D l U₀ iota M = (w : EReal) :=
    l2Weight_eq_of_pure D l _hl iota U₀ j₀ M _hlisse _hne w _hpure
  obtain ⟨hle, hbound⟩ :=
    middle_traceEnergy_bounds D l _hl iota U₀ j₀ M _hlisse w _hpure
  have hq : (1 : ℝ) < D.q := by
    rw [← D.card_base]
    exact_mod_cast (Finite.one_lt_card (α := D.k₀))
  have heq := weightOfEnergy_eq_of_sandwich D.q hq
    (traceEnergy D l U₀ iota M)
    (traceEnergy D l C₀ iota (middleWeilImage D l j₀ M)) w hpure hle hbound
  exact ⟨heq, hpure⟩

end WeilConjectures.NativeL2
