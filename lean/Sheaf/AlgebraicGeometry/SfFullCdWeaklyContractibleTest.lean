/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.ProEtaleVanishingDetection

/-!
# Testing FullCD on affine weakly contractible objects

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-fullcd-etale-origin,
order 1793 (blueprint: cor-sf-fullcd-weakly-contractible-test).

The test evaluates cohomology sheaves and includes the relative clause with sheaves
pulled back from the original source. It does not require geometric-point stalks.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- FullCD is equivalent to vanishing of the indicated cohomology-sheaf sections on
all affine weakly contractible objects, both absolutely and after each pro-etale
base change. Weak contractibility uses the existing site predicate: local surjectivity
of a set-sheaf morphism is equivalent to being an epimorphism. The coefficient ring
is the recorded finite quotient, regarded as discrete through the constant sheaf.

Source: Weil blueprint, order 1793
(blueprint: cor-sf-fullcd-weakly-contractible-test).

Proof:
1. For every original-source sheaf F and r > c, apply clause (i) of
   lem-sf-proetale-vanishing-detection to the module sheaf H^r(Rp_* F) on Y.
   A sheaf is zero exactly when its sections on every affine weakly contractible
   object vanish. The coefficients are finite by finite_coefficientExtensionRing.
2. Fix an arbitrary V in Y_proet and apply the same detection lemma on V to
   H^r(R(p_V)_*(g_V^* F)). Here F is still a sheaf on the original source X;
   g_V^* is the canonical module-sheaf pullback along pullback.fst p V.hom.
   No finite-type assumption on V or its fiber product is required for detection.
   Quantify over V, F, and r > c, and combine with the first step to obtain the
   two conjuncts of sfFullCohomologicalDimension.
3. These arguments only evaluate cohomology sheaves; they never compute geometric
   stalks or replace these sections by ordinary evaluations of a chosen complex.
   Thus the general nonconservativity warning in clause (4) of
   lem-cbc-proetale-stalk-conservative does not obstruct this test, including for
   the empty base scheme. -/
theorem sfFullCohomologicalDimension_iff_weaklyContractible_test
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (S : Scheme.{u}) (_hl : IsUnit (l : Γ(S, ⊤)))
    {X Y : Scheme.{u}} (aX : X ⟶ S) (aY : Y ⟶ S)
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (p : X ⟶ Y) [IsProper p] (_hp : p ≫ aY = aX) (c : ℕ) :
    sfFullCohomologicalDimension p (Padic.coefficientExtensionRing l E n) c ↔
      (∀ (F : proEtaleRingModules X
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)))
        (W : Y.ProEt), IsAffine W.left →
        (ProEt.topology Y).IsWeaklyContractible.{u + 1} W →
        ∀ r : ℤ, (c : ℤ) < r →
          Subsingleton (((DerivedCategory.homologyFunctor _ r).obj
            ((proEtaleConstantDerivedDirectImage p
              (Padic.coefficientExtensionRing l E n)).obj
              ((DerivedCategory.singleFunctor _ 0).obj F))).val.obj (op W))) ∧
      ∀ (V : Y.ProEt)
        (F : proEtaleRingModules X
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)))
        (W : V.left.ProEt), IsAffine W.left →
        (ProEt.topology V.left).IsWeaklyContractible.{u + 1} W →
        ∀ r : ℤ, (c : ℤ) < r →
          Subsingleton (((DerivedCategory.homologyFunctor _ r).obj
            ((proEtaleConstantDerivedDirectImage (pullback.snd p V.hom)
              (Padic.coefficientExtensionRing l E n)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (proEtaleConstantModulePullback (pullback.fst p V.hom)
                  (Padic.coefficientExtensionRing l E n) F)))).val.obj (op W)) := by
  sorry

end AlgebraicGeometry.Scheme
