/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.TraceFormulaLocalFrobeniusOperator
public import Sheaf.TraceFormula.PointTransportComposition
import Sheaf.Paper.FrobeniusPullbackComparisonCoherence
import Sheaf.CategoryTheory.NaturalTransportInduction
import Sheaf.Paper.IteratedWeilCocycle
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.Paper.IteratedWeilMap
import Sheaf.Paper.TraceFormulaCoefficientConventions
import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso
import Sheaf.SixFunctors.SchemeFrobenius
import Sheaf.TraceFormula.CompactFrobeniusTransportComposition

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

/-- The direct compact-support transport along `g^(r+1)`: restriction, colimit
insertion and derived pullback at the point, followed by the fibre of the specified
proper/open exchange. The geometric compactification is fixed over k₀ for every power.
The square witnesses are pasted from the existing degree-one Cartesian squares.
Source: main-20261015 blueprint, compact-support description, displayed formula;
Deligne, Weil II (1.1.10)--(1.1.14)
(blueprint: lem-trf-frobenius-operator-compact-description). -/
def finiteGlobalDirectPowerTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) (r : ℕ) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower r).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E
    let A := Padic.coefficientExtensionRing C.l F (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing C.l F (n + 1) hn
    let c := frobeniusCohomologyCompactification D X c₀
    let gX : End (D.geometricFiber X).left := galois D X
    let gB : End c.Z :=
      galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X) c₀)
    let h := pointFrobeniusAut D
    have sp₁ : IsPullback gB c.g c.g h.hom :=
      (D.frobenius_square_cartesian
        (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X) c₀)
        (sfWeilCohomologyPoint D)
        (zlCompactificationProper D (frobeniusCohomologyModelMap D X) c₀)).2.2.2.2.2.2.2
    have sj₁ : IsPullback gX c.i c.i gB :=
      (D.frobenius_square_cartesian X
        (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X) c₀)
        (zlCompactificationOpen D (frobeniusCohomologyModelMap D X) c₀)).2.2.2.2.2.1
    have sp : ∀ m : ℕ, IsPullback (gB ^ m) c.g c.g (h ^ m).hom := by
      intro m
      induction m with
      | zero => exact IsPullback.id_horiz _
      | succ m ih =>
        simpa only [pow_succ, End.mul_def, Aut.Aut_mul_def, Iso.trans_hom] using
          sp₁.paste_horiz ih
    have sj : ∀ m : ℕ, IsPullback (gX ^ m) c.i c.i (gB ^ m) := by
      intro m
      induction m with
      | zero => exact IsPullback.id_horiz _
      | succ m ih =>
        simpa only [pow_succ, End.mul_def] using sj₁.paste_horiz ih
    let H := sfIntrinsicCompactSupport c A
    let e := finiteCompact C.l F (n + 1) hn c (gX ^ (r + 1)) (gB ^ (r + 1))
      (h ^ (r + 1)).hom (sp (r + 1)).w (sj (r + 1))
    exact pointPowerTransportFinite D C.l C.different F (r + 1) n (H.obj M) ≫
      (finiteLocalSections ⟨D, C, E, n + 1, hn, X⟩).map
        ((pointPowerPullbackModel C.l F n (h ^ (r + 1)).hom).hom.app (H.obj M) ≫
          e.app M)

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
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
