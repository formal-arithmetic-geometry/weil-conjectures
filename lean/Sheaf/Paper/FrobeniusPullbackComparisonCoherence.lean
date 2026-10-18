/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Coherence of Frobenius-power pullback comparisons

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, the m-th-iterate assertion;
Stacks Project, Tag 0D6D
(blueprint: lem-trf-frobenius-pullback-comparison-coherence).

Positive exponents are indexed by their predecessor: index `r` means exponent `r + 1`.
The two binary-splitting equations encode every ordered splitting tree, and hence every
finite positive partition and reassociation. Both orders of refining the two branches
are displayed. All helpers construct the comparisons explicitly, without choosing maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The prescribed powers `T^1 = T`, `T^(r+1) = T ∘ T^r`.
Source: blueprint, m-th-iterate assertion
(blueprint: lem-trf-frobenius-pullback-comparison-coherence). -/
def trfPositiveFunctorPower {C : Type v} [Category.{w} C] (T : C ⥤ C) : ℕ → C ⥤ C
  | 0 => T
  | r + 1 => trfPositiveFunctorPower T r ⋙ T

/-- The reassociation `T^(a+b) ≅ T^a ∘ T^b` made only of canonical associators.
The indices `a,b` denote the positive exponents `a+1,b+1`.
Source: blueprint, m-th-iterate assertion
(blueprint: lem-trf-frobenius-pullback-comparison-coherence). -/
def trfPositiveFunctorPowerSplit {C : Type v} [Category.{w} C] (T : C ⥤ C) :
    (a b : ℕ) → trfPositiveFunctorPower T (b + a + 1) ≅
      trfPositiveFunctorPower T b ⋙ trfPositiveFunctorPower T a
  | 0, _b => Iso.refl _
  | a + 1, b =>
      Functor.isoWhiskerRight (trfPositiveFunctorPowerSplit T a b) T ≪≫
        Functor.associator _ _ _

namespace TraceFormulaCoefficientConventions

/-- The actual ordinary pullback `P_(r+1) = L(g^(r+1))^*`, for geometric Galois Frobenius.
This is the recorded `geometricGaloisDerivedPullback` of def-trf-scheme-frobenius at
exponent `r + 1`, i.e. `proEtaleConstantRingDerivedPullback` along `g^(r+1)`.
Source: blueprint, m-th-iterate assertion
(blueprint: lem-trf-frobenius-pullback-comparison-coherence). -/
abbrev frobeniusPullbackPower (S : TraceFormulaCoefficientConventions.{u}) (r : ℕ) :=
  S.datum.geometricGaloisDerivedPullback S.X₀ S.coefficientRing (r + 1)

/-- The normalized composition comparison `C_(a+1,b+1)` for actual powers of `g`.
Only the power-addition equality is transported; the natural isomorphism is the published
constant-coefficient specialization of the K-flat-normalized comparison of Tag 0D6D.
Source: blueprint, m-th-iterate assertion; Stacks Project, Tag 0D6D
(blueprint: lem-trf-frobenius-pullback-comparison-coherence). -/
def frobeniusPullbackPowerSplit (S : TraceFormulaCoefficientConventions.{u}) (a b : ℕ) :
    S.frobeniusPullbackPower (b + a + 1) ≅
      S.frobeniusPullbackPower b ⋙ S.frobeniusPullbackPower a :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback S.coefficientRing)
    (by
      change (End.of (S.datum.geometricGaloisFrobenius S.X₀)) ^ (b + a + 1 + 1) =
        (End.of (S.datum.geometricGaloisFrobenius S.X₀)) ^ (b + 1) *
          (End.of (S.datum.geometricGaloisFrobenius S.X₀)) ^ (a + 1)
      rw [show b + a + 1 + 1 = (b + 1) + (a + 1) by omega, pow_add])) ≪≫
    (proEtaleConstantRingPullbackComposition
      ((End.of (S.datum.geometricGaloisFrobenius S.X₀)) ^ (a + 1))
      ((End.of (S.datum.geometricGaloisFrobenius S.X₀)) ^ (b + 1))
      S.coefficientRing).symm

/-- The recursive comparison `d_1 = id`, `d_(r+1) = T(d_r) ∘ C_(1,r)`.
It is built from actual comparison isomorphisms, never from an existence choice.
Source: blueprint, m-th-iterate assertion
(blueprint: lem-trf-frobenius-pullback-comparison-coherence). -/
def frobeniusPullbackPowerComparison (S : TraceFormulaCoefficientConventions.{u}) :
    (r : ℕ) → S.frobeniusPullbackPower r ≅
      trfPositiveFunctorPower (S.frobeniusPullbackPower 0) r
  | 0 => Iso.refl _
  | r + 1 => S.frobeniusPullbackPowerSplit 0 r ≪≫
      Functor.isoWhiskerRight (S.frobeniusPullbackPowerComparison r) (S.frobeniusPullbackPower 0)

/-- Every repeated positive splitting gives the same normalized comparison `d_r`.
The first clause is the identity at exponent one. The next two equations identify both
orders of splitting the two branches at every binary vertex with `d_(a+b)` after the
canonical reassociation. Induction over a finite splitting tree is exactly independence
for an arbitrary positive partition, its parenthesization and its refinement order.
The last equation is `d_(r+1)^(-1) ∘ T(d_r) = b_r` on every unbounded derived object.
Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, m-th-iterate assertion;
Stacks Project, Tag 0D6D
(blueprint: lem-trf-frobenius-pullback-comparison-coherence).

Proof: (1) Work in the ordinary unbounded pro-etale derived category with the constant
ring `A = O_E / ϖ_E^n`, finite by def-weil-l-adic-coefficient-extension. The canonical
coefficient identification composes by lem-trf-constant-coefficient-composition, so the
comparisons of lem-weil-pbc-proetale-derived-pullback-composition apply unchanged.
(2) Apply lem-trf-derived-pullback-coherence to three positive powers of geometric
Frobenius. The associators have identity components and give the triple cocycle.
(3) Define `d` by the displayed recursion, starting with the identity at exponent one;
composition and whiskering preserve natural isomorphisms.
(4) Induct on the first positive summand to obtain binary compatibility. At summand one
this is the recursion. In the successor step expand the recursion and the induction
hypothesis, use the triple cocycle at `(1,a-1,b)`, then combine the middle factors by
the recursion for `d_a`. This is an equality of natural transformations.
(5) Induct over each ordered splitting tree. Both subtree weights are smaller than
the root weight, so their comparisons are `d_a,d_b`; step (4) identifies the root map
with `d_(a+b)`. Naturality of `d_a` at `d_b` interchanges the two orders of refinement.
The same interchange inside each functor context covers arbitrary refinement orders;
canonical associators account for all parenthesizations and multiway positive splits.
(6) Invert the successor recursion and cancel `T(d_r)` using functoriality and the
inverse laws. This gives the last equation, also at r=1 and on the empty scheme. -/
theorem frobenius_pullback_comparison_coherence (S : TraceFormulaCoefficientConventions.{u}) :
    S.frobeniusPullbackPowerComparison 0 = Iso.refl (S.frobeniusPullbackPower 0) ∧
    (∀ a b : ℕ,
      S.frobeniusPullbackPowerComparison (b + a + 1) ≪≫
          trfPositiveFunctorPowerSplit (S.frobeniusPullbackPower 0) a b =
        S.frobeniusPullbackPowerSplit a b ≪≫
          Functor.isoWhiskerLeft (S.frobeniusPullbackPower b)
            (S.frobeniusPullbackPowerComparison a) ≪≫
          Functor.isoWhiskerRight (S.frobeniusPullbackPowerComparison b)
            (trfPositiveFunctorPower (S.frobeniusPullbackPower 0) a) ∧
      S.frobeniusPullbackPowerComparison (b + a + 1) ≪≫
          trfPositiveFunctorPowerSplit (S.frobeniusPullbackPower 0) a b =
        S.frobeniusPullbackPowerSplit a b ≪≫
          Functor.isoWhiskerRight (S.frobeniusPullbackPowerComparison b)
            (S.frobeniusPullbackPower a) ≪≫
          Functor.isoWhiskerLeft (trfPositiveFunctorPower (S.frobeniusPullbackPower 0) b)
            (S.frobeniusPullbackPowerComparison a)) ∧
    (∀ (r : ℕ) (M : proEtaleDerivedCategory S.geometricBaseChange S.coefficientRing),
      (S.frobeniusPullbackPower 0).map ((S.frobeniusPullbackPowerComparison r).hom.app M) ≫
          (S.frobeniusPullbackPowerComparison (r + 1)).inv.app M =
        (S.frobeniusPullbackPowerSplit 0 r).inv.app M) := by
  sorry

end TraceFormulaCoefficientConventions
end WeilConjectures
