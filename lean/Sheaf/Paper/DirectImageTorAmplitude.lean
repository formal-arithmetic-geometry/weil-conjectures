/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.CategoryTheory.TruncationHypercohomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest

/-!
# Direct image and finite Tor amplitude

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
`thm-sf-direct-image-tor-amplitude.md` (blueprint: thm-sf-direct-image-tor-amplitude).

The uniform cohomological-dimension hypothesis tests all ordinary etale module sheaves
for the present field. Both conclusions concern the ordinary derived direct image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Direct image sends a bounded constructible complex of Tor amplitude `[a,b]` to a
bounded constructible complex of Tor amplitude `[a,b+N]`, assuming uniform vanishing
above `N` on every module sheaf.
Source: Weil blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
`thm-sf-direct-image-tor-amplitude.md` (blueprint: thm-sf-direct-image-tor-amplitude).

Proof plan:
1. The coefficient conventions and lem-weil-l-adic-extension-integers-dvr make the
integer ring a DVR with finite residue field. By lem-weil-valued-dvr-finite-quotients,
A is finite local, hence Noetherian. The extended valuation gives l in (uniformizer),
so l^n A = 0; l^n is invertible in k by the characteristic assumption.
2. Put L = K tensor^L kappa_X. By def-kun-tor-amplitude its cohomology vanishes
outside [a,b]. Good lower truncation at a supplies a bounded-below representative:
zero below a, coker of the preceding differential at a, and the original terms above a.
3. Module sheaves are Grothendieck abelian by
lem-weil-pbc-module-sheaves-grothendieck-abelian; direct image is additive and left exact
by lem-weil-pbc-module-direct-image-left-exact. Apply thm-sp-truncation-e2 to obtain
E2^{p,q} = R^p f_* H^q(L), abutting to H^{p+q}(Rf_*L), with finite exhaustive
separated filtrations. Negative p columns vanish.
4. Uniform vanishing and Step 2 support this page in 0 <= p <= N and a <= q <= b.
Outside total degrees [a,b+N], all stable entries vanish. Induction over the finite
abutment filtration gives zero cohomology there.
5. Apply thm-dg-finite-type-constructibility with the finite ring A, annihilated by
l^n invertible in k, to obtain bounded constructibility of F = Rf_*K.
6. The presentation A --uniformizer--> A --> kappa --> 0 is finite. Apply
lem-sf-projection-finite-constant, using the uniform bound, Noetherian A and bounded K.
The canonical map of def-kun-projection-formula-map identifies F tensor^L kappa_Y
with Rf_*L. The unbounded direct image and def-weil-pbc-direct-image agree on these
bounded-below objects because both are computed by the same K-injective resolutions.
Thus the residue tensor has cohomology only in [a,b+N].
7. Apply lem-exc-residue-tor-test to the bounded constructible F and this residue-tensor
vanishing to conclude the asserted Tor amplitude. Together with Step 5 this proves
both clauses. -/
theorem sf_directImage_torAmplitude
    (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (N : ℤ) (_hN : 0 ≤ N)
    (_hUDV : ∀ (M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (r : ℤ), N < r →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (_hK : @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      _ (Padic.finite_coefficientExtensionRing l E n hn) X K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) X a b K) :
    @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
        _ (Padic.finite_coefficientExtensionRing l E n hn) Y
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a (b + N)
        ((rightDerivedLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) f).obj K) := by
  sorry

end AlgebraicGeometry.Etale
