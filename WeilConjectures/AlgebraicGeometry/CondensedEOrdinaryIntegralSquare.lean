/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealizationDefinitions
public import WeilConjectures.AlgebraicGeometry.CondensedEExchangeMate
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.PbcActualRingedExchange
import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.CompletedConstantPresentationTransport
import WeilConjectures.AlgebraicGeometry.IntegralFinitePullbackComposition

/-! # Ordinary and integral pullback squares

Source: Stacks Project, Tag 07A7, remark-base-change; the normalized realization
records and CompletedExchangeCoherence.completedPullComp_existsUnique.
(blueprint: lem-weil-pbc-condensed-e-ordinary-integral-square).

The comparison is the completion unit followed by the inverse ambient inclusion
comparison. The theorem compares the ordinary ringed square with integralSquare.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CondensedERealization

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
variable (D : Data l E k)

/-- The node's comparison a_h is the specified completion unit followed by A_h inverse.
Source: Stacks Tag 07A7; normalized realization records, Along.pullAmbient.
(blueprint: lem-weil-pbc-condensed-e-ordinary-integral-square). -/
def ordinaryToIntegralPull (T V : Base k) (h : T.scheme ⟶ V.scheme)
    [h.IsOver (Spec (.of k))] (M : Integral l E V.scheme) :
    ((pbcIntegralDatum l E).pull h).obj M.obj ⟶ ((D.along T V h).pull.obj M).obj :=
  (pbcIntegralDatum l E).ordinaryToCompleted h M.obj ≫
    (D.along T V h).pullAmbient.inv.app M

variable {X' X Y' Y : Base k}
variable {g' : X'.scheme ⟶ X.scheme} {f' : X'.scheme ⟶ Y'.scheme}
  {f : X.scheme ⟶ Y.scheme} {g : Y'.scheme ⟶ Y.scheme}
variable [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- The completion-unit comparison carries the ordinary pullback square to integralSquare.
Source: Stacks Tag 07A7, remark-base-change; normalized realization Data.integralComp_normalization
and CompletedExchangeCoherence.completedPullComp_existsUnique.
(blueprint: lem-weil-pbc-condensed-e-ordinary-integral-square).

Proof: write c_o, c_F and c_I for the ordinary, completed and integral compositors.
The unique unit-normalized completed compositor satisfies
j_(jh);c_F = c_o;L_h(j_j);j_h(F_j(-)). The intrinsic-complete reflector model has
this property by lem-route-pbc-actual-completed-pull-comp-iso-exists. The quotient
and intrinsic completeness conditions agree by completed-constant-presentation-transport:
the same equivalence carries both units to the constant completion unit. The completed
pullback construction and completed-pullback-reflection therefore identify the two
reflectors preserving their units: each universal property supplies a map, and
injectivity of unit precomposition makes these maps inverse and natural. Ordinary
composition is the canonical K-flat comparison of proetale-derived-pullback-composition.
Thus the reflector comparison gives the normalization defining completedPullComp.
Next integralComp_normalization says U(c_I);A_h;F_h(A_j) = A_(jh);c_F.
Since a_h;A_h = j_h, postcompose by the invertible A_h;F_h(A_j).
Naturality of j_h at A_j and the completed normalization give
 a_(jh);U(c_I) = c_o;L_h(a_j);a_h(P_j(-)).
Only ambient comparison isomorphisms are cancelled; no completion unit is cancelled.
Apply this identity to (f',g) and (g',f). Equality elimination along the equality
of bundled k-morphisms gives t_o;a_(fg') = a_(gf');U(t_I).
Compose with the inverse (f',g) compositor and the (g',f) compositor, cancelling
adjacent inverse isomorphisms. The ordinary composite is exactly the ringed
pullback comparison with the same coefficient transports. The integral composite
is integralSquare by its definition. This yields the displayed equality. -/
theorem ordinaryIntegralSquare (sq : ChosenCartesianSquare g' f' f g)
    (M : Integral l E Y.scheme) :
    (proEtaleAmbientRingedPullbackComparison sq
      ((pbcIntegralDatum l E).completedRing X.scheme)
      ((pbcIntegralDatum l E).completedRing Y.scheme)
      ((pbcIntegralDatum l E).completedRing X'.scheme)
      ((pbcIntegralDatum l E).completedRing Y'.scheme)
      ((pbcIntegralDatum l E).integralRingIso f)
      ((pbcIntegralDatum l E).integralRingIso g)
      ((pbcIntegralDatum l E).integralRingIso g')
      ((pbcIntegralDatum l E).integralRingIso f')
      ((pbcIntegralDatum l E).integral_coherent sq)).hom.app M.obj ≫
        ((pbcIntegralDatum l E).pull g').map (ordinaryToIntegralPull l E k D X Y f M) ≫
        ordinaryToIntegralPull l E k D X' X g' ((D.along X Y f).pull.obj M) =
      ((pbcIntegralDatum l E).pull f').map (ordinaryToIntegralPull l E k D Y' Y g M) ≫
        ordinaryToIntegralPull l E k D X' Y' f' ((D.along Y' Y g).pull.obj M) ≫
        ((integralSquare l E k D sq.toCommSq).hom.app M).hom := by
  sorry

end WeilConjectures.CondensedERealization
