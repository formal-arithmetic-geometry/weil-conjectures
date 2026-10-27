/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.TraceFormulaLocalFrobeniusOperator
public import Sheaf.TraceFormula.PointTransportComposition
public import Sheaf.TraceFormula.CompactDirectPowerTransportNormalization
import Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence

/-!
# Compact-support description of global geometric Frobenius

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description
(blueprint: lem-trf-frobenius-operator-compact-description).

The direct transport uses the exchange for the power square with the same retained
compactification. It is constructed separately from repeated degree-one transport.
The nonnegative index `r` denotes the positive exponent `m = r+1` throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions
open FrobeniusExchange

private theorem transport_powers {C : Type*} [Category C] {X : C}
    (f : ℕ → End X) (hf : ∀ i : ℕ, f (i + 1) = f i ≫ f 0) (r : ℕ) :
    f r = f 0 ^ (r + 1) := by
  induction r with
  | zero => exact (pow_one _).symm
  | succ r ih => rw [hf, ih, ← End.mul_def, ← pow_succ']

/-- The direct compact-support transport along `g^(r+1)`: restriction, colimit
insertion and derived pullback at the point, followed by the fibre of the specified
proper/open exchange. The geometric compactification is fixed over k₀ for every power.
The power squares and their witnesses are those of the canonical direct transport.
Source: main-20261015 blueprint, compact-support description, displayed formula;
Deligne, Weil II (1.1.10)--(1.1.14)
(blueprint: lem-trf-frobenius-operator-compact-description). -/
abbrev finiteGlobalDirectPowerTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) (r : ℕ) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower r).obj M) :=
  T.compactDirectPowerTransport c₀ M r

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] sfIntrinsicCompactSupport Functor.mapDerivedCategory
  pointFiniteSections finiteGlobalFrobenius finiteGlobalComparedTransport
  compactDirectPowerTransport

attribute [local irreducible] iteratedWeilIsomorphism pointPowerPullbackModel

attribute [local irreducible] compactPowerTransport

private theorem global_as_direct (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex) (r : ℕ) :
    T.finiteGlobalFrobenius c₀ K r = T.compactDirectPowerTransport c₀ K.obj.carrier r ≫
      (T.finiteGlobalCompactSections c₀).map
        (T.iteratedWeilIsomorphism K (r + 1) (Nat.succ_pos r)).hom := by
  unfold finiteGlobalFrobenius
  exact congrArg (fun f ↦ f ≫ (T.finiteGlobalCompactSections c₀).map
    (T.iteratedWeilIsomorphism K (r + 1) (Nat.succ_pos r)).hom)
    (compact_direct_power_transport_normalization T c₀
      ⟨K.obj.carrier, K.property.1⟩ r).2.2.1

private theorem direct_as_cocycle (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (c₀ : Compactification X.hom) (n : ℕ)
    (K : (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n)
      X).strictWeilComplex) (j : ℕ) :
    compactDirectPowerTransport
        (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n) X)
        c₀ K.obj.carrier j ≫
      (finiteGlobalCompactSections
        (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n) X) c₀).map
        (iteratedWeilIsomorphism
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n) X)
          K (j + 1) (Nat.succ_pos j)).hom =
      compactWeilCocycleEndomorphism D C E X c₀ n K (j + 1) (Nat.succ_pos j) := by
  unfold compactDirectPowerTransport compactWeilCocycleEndomorphism
  dsimp only [Nat.casesAuxOn, compactPowerCohomology, finiteGlobalCompactSections,
    finiteLocalSections, TraceFormulaCoefficientConventions.coefficientRing,
    TraceFormulaCoefficientConventions.coefficientField]
  exact Category.assoc _ _ _ |>.trans
    (congrArg (_ ≫ ·) (Functor.map_comp
      (finiteGlobalCompactSections
        (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n) X) c₀)
      _ _).symm)

attribute [local irreducible] compactWeilCocycleEndomorphism

/-- On the actual compact-support complex the operator defined by repeated transport
is its indicated positive power and is the direct-power base-change composite.
The direct first arrow is an isomorphism, as required by the statement.
Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description, statement and proof;
Deligne, Weil II (1.1.10)--(1.1.14)
(blueprint: lem-trf-frobenius-operator-compact-description).

Proof: (1) Expand clause 1 of def-trf-frobenius-operators at m=1. It is H(phi)
after the degree-one compact transport of def-weil-frobenius-cohomology-transport,
which is the point transport followed by Fib of the retained-compactification exchange.
(2) Powers of g are isomorphisms. The finite part of
lem-weil-isomorphism-derived-pullback preserves bounded constructibility, and clause 3
of lem-weil-frobenius-cohomology-transport-iso makes degree-one transports invertible.
Use lem-trf-compact-frobenius-transport-composition with the fixed compactification:
tau_(r+1) = H(b_r) tau_(1,P_r M) tau_r. This also proves invertibility by induction.
(3) The comparisons d_r are those of def-trf-frobenius-operators. Their normalization
and d_(r+1)^(-1) T(d_r) = b_r are
lem-trf-frobenius-pullback-comparison-coherence. Apply
lem-trf-frobenius-transport-induction using naturality of degree-one transport to
identify the repeated transport followed by H(d_r^(-1)) with direct tau_r.
(4) Put T_r = H(phi^[r]) tau_r. The cocycle of lem-trf-iterated-weil-cocycle at (1,r)
gives phi^[r+1] b_r = phi P_1(phi^[r]). Naturality at u = phi^[r] gives
H(P_1 u) tau_(1,P_r K) = tau_(1,K) H(u). Substituting these and the recurrence yields
T_(r+1) = H(phi) tau_(1,K) H(u) tau_r = T_1 T_r.
(5) Induct from T_1 = F_c to obtain T_r = F_c^r. Step (3) identifies the first arrow
in the defined operator with direct compact-support base change, giving the formula
on complexes, before applying any cohomology functor. -/
theorem frobenius_operator_compact_description (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex) (r : ℕ) :
    T.finiteGlobalFrobenius c₀ K r = (T.finiteGlobalFrobenius c₀ K 0) ^ (r + 1) ∧
    T.finiteGlobalFrobenius c₀ K r =
      T.finiteGlobalDirectPowerTransport c₀ K.obj.carrier r ≫
        (T.finiteGlobalCompactSections c₀).map
          (T.iteratedWeilIsomorphism K (r + 1) (Nat.succ_le_succ (Nat.zero_le r))).hom ∧
    IsIso (T.finiteGlobalDirectPowerTransport c₀ K.obj.carrier r) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    have hnorm := compact_direct_power_transport_normalization
      ⟨D, C, E, n + 1, hn, X⟩ c₀ ⟨K.obj.carrier, K.property.1⟩ r
    have hrec := compact_weil_cocycle_endomorphism_recurrence
      D C E X c₀ n K
    have hU (j : ℕ) :
        finiteGlobalFrobenius
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) hn X) c₀ K j =
        compactWeilCocycleEndomorphism D C E X c₀ n K (j + 1) (Nat.succ_pos j) :=
      (global_as_direct _ c₀ K j).trans (direct_as_cocycle D C E X c₀ n K j)
    have hstep (i : ℕ) :
        finiteGlobalFrobenius
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) hn X) c₀ K (i + 1) =
        finiteGlobalFrobenius
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) hn X) c₀ K i ≫
        finiteGlobalFrobenius
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) hn X) c₀ K 0 := by
      exact (hU (i + 1)).trans ((hrec.2 (i + 1) (Nat.succ_pos i)).trans
        (congrArg₂ (fun f g ↦ f ≫ g) (hU i).symm (hU 0).symm))
    refine ⟨?_, ?_, ?_⟩
    · exact transport_powers
        (X := (finiteGlobalCompactSections
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) hn X) c₀).obj K.obj.carrier)
        (fun i ↦ finiteGlobalFrobenius
          (TraceFormulaCoefficientConventions.mk D C E (n + 1) hn X) c₀ K i) hstep r
    · exact global_as_direct _ c₀ K r
    · exact hnorm.2.2.2.2

end WeilConjectures.TraceFormulaCoefficientConventions
