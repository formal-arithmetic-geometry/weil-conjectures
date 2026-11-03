/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.AffineSpace.GeometricallyConnected

/-! Finite-boundary energy estimate for the native middle image.
Source: latest blueprint, lem-fd-l2-middle-extension.proof.md, first two paragraphs.
(blueprint: lem-fd-native-l2-middle-energy-bound).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

local instance middleEnergy_affineLineModel_locallyOfFiniteType (D : FiniteFieldDatum.{u}) :
    LocallyOfFiniteType (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (affineLine D.k₀ ↘ Spec (.of D.k₀)))

local instance middleEnergy_affineLineModel_quasiCompact (D : FiniteFieldDatum.{u}) :
    QuasiCompact (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))).hom :=
  inferInstanceAs (QuasiCompact (affineLine D.k₀ ↘ Spec (.of D.k₀)))

/-- The open and middle-image energies differ by a nonnegative boundary contribution
bounded by C q^(mw).

Source: latest blueprint, lem-fd-l2-middle-extension.proof.md, opening and middle
paragraphs (blueprint: lem-fd-native-l2-middle-energy-bound).

Proof: the canonical open restriction is Weil compatible, hence the two stalk operators
are conjugate at points of U₀ and traces of all their powers agree. Split the rational
point sum into U₀ and its finite complement S₀. Equivalently split the closed-point sum,
retaining the multiplicity d(s) for d(s) dividing m. The difference E_m is a sum of
nonnegative squared traces. At each boundary point s the invariant-stalk identification
bounds the dimension by the lisse rank r. Purity on U₀ and boundary semicontinuity
bound each squared eigenvalue norm by q^(d(s)w). The condensed local-Frobenius powers
identify the extension-field operator with the (m/d(s))-th closed Frobenius power.
Thus each eigenvalue power has squared norm at most q^(mw); the triangle inequality
bounds the squared trace by r² q^(mw). The finite boundary point count is at most
D=sum_s d(s). Therefore E_m ≤ D r² q^(mw), and C=D r² works for every positive m.
At m=0 both energies are zero. Empty boundary, zero rank, and negative w satisfy the
same formulas. No purity-rigidity or limsup comparison is used in this estimate. -/
theorem middle_traceEnergy_bounds
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (iota : PadicAlgCl l →+* ℂ)
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (j₀ : U₀ ⟶ Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀)))
    [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (_hlisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (w : ℝ) (_hpure : Pure D l U₀ M iota w) :
    (∀ m : ℕ, traceEnergy D l U₀ iota M m ≤
      traceEnergy D l (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))) iota
        (middleWeilImage D l j₀ M) m) ∧
    (∃ C : ℝ, ∀ m : ℕ,
      traceEnergy D l (Over.mk (affineLine D.k₀ ↘ Spec (.of D.k₀))) iota
          (middleWeilImage D l j₀ M) m ≤
        traceEnergy D l U₀ iota M m + C * (D.q : ℝ) ^ ((m : ℝ) * w)) := by
  sorry

end WeilConjectures.NativeL2
