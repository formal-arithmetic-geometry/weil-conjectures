/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural

/-! # Naturality of iterated local Frobenius for morphisms of Weil pairs

Source: Weil blueprint, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed local alternating-trace formula, with its agent-extracted naturality argument
(blueprint: lem-fd-local-frobenius-weil-morphism-naturality).

The auxiliary abbreviations specialize the published pullback functor with its inherited
prime-invertibility instances. The return comparison and transport extend the published
local construction to every constructible object, without requiring a Weil structure.
All positive-power indices below denote exponent one greater than the index.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The specified pullback S_(r+1) on the point, with inherited invertibility.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
abbrev localPointPowerPullback (r : ℕ) :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (frobeniusPointIso D).hom r)
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The specified pullback G_(r+1) on the geometric fibre, with inherited invertibility.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
abbrev localGeometricPowerPullback (r : ℕ) :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (D.geometricFrobenius X₀).hom r)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

/-- The specified pullback P at an arbitrary geometric point, on the full constructible domain.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
abbrev localConstructibleStalkFunctor
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)

/-- The specified return comparison rho, on every constructible object M.
This is the same composite as localReturnComparison, with no Weil structure required.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
def localConstructibleReturnComparison
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (localPointPowerPullback l E D hl r).obj
        ((localConstructibleStalkFunctor l E D hl X₀ x).obj M) ≅
      (localConstructibleStalkFunctor l E D hl X₀ x).obj
        ((localGeometricPowerPullback l E D hl X₀ r).obj M) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl X₀
  (localPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom r)
    x M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M) h.symm) ≪≫
    localPullbackComposition l E x
      (localPositivePower (D.geometricFrobenius X₀).hom r) M

/-- The specified R(M) = Q(rho_M) I^[r+1]_(P(M)), on every constructible object.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
def localConstructibleReturnTransport
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  localPointTransportIterate l E D hl
      ((localConstructibleStalkFunctor l E D hl X₀ x).obj M) r ≫
    (pointRationalFibre D l hl E).map
      (localConstructibleReturnComparison l E D hl X₀ x r h M).hom

/-- Naturality on the full raw rationalized constructible domain, including arbitrary
(noninvertible) morphisms of Weil pairs. Each r : ℕ denotes the positive exponent r+1.
Source: blueprint sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed alternating-trace formula, agent-extracted comparison lemma
(blueprint: lem-fd-local-frobenius-weil-morphism-naturality).

Proof:
1. The rational clause of lem-weil-frobenius-point-transport-natural gives the single-step
   naturality square for every rational constructible arrow w, including all its pullbacks.
   The functor Q is clause 3 of def-weil-finite-coefficient-point.
2. Induct on the positive exponent to compose these squares. Conjugate the iterated
   one-step pullback by the specified composition comparison. Its rational naturality and
   iteration compatibility are lem-trf-integral-pullback-comparison-realization. This gives
   Q(S_r(w)) I_N^[r] = I_N'^[r] Q(w).
3. The return equality identifies the sources of the two specified composition comparisons
   a : H ≅ S_n P and b : H ≅ P G_n. The return is b a⁻¹. Their naturality squares give
   P(G_n(v)) rho_M = rho_M' S_n(P(v)). This uses the actual semilinear return equality,
   not a fixed geometric-point equation.
4. Apply Q to step 3, multiply by I^[n], and use step 2 for P(v). Functoriality yields
   D(G_n(v)) R(M) = R(M') D(v).
5. The Weil-pair morphism equation is the exponent-one base. In the recursion
   alpha^[r+1] = alpha^[r] G_r(alpha) k_r, insert the induction hypothesis, use the
   one-step equation under G_r, and then naturality of the specified k_r. This proves
   v alpha^[r] = beta^[r] G_r(v) for every positive r.
6. Apply D to step 5 at n and multiply by R(A). Step 4 turns the result into the local
   operator intertwining equation. No inverse of v, Weil-stable integral lattice or
   finite-reduction Tor-amplitude condition is used. -/
theorem localFrobeniusWeilMorphismNaturality
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (F : Padic.FiniteCoefficientFields c.l c.Qbar)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) :
    (∀ (r : ℕ) (N N' : sfRationalConstructibleCategory c.l F.val (Spec (.of D.k)))
      (w : N ⟶ N'),
      (localPointTransportIterate c.l F.val D c.different N r) ≫ (pointRationalFibre D c.l
          c.different F.val).map ((localPointPowerPullback c.l F.val D c.different r).map w) =
        (pointRationalFibre D c.l c.different F.val).map w ≫ (localPointTransportIterate c.l F.val D
          c.different N' r)) ∧
    (∀ (M M' : sfRationalConstructibleCategory c.l F.val (D.geometricFiber X₀).left)
      (v : M ⟶ M'),
      (localConstructibleReturnComparison c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x) (n - 1) (localExtensionPoint_return D X₀ n hn x) M).hom ≫
          (localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)).map ((localGeometricPowerPullback c.l F.val D c.different X₀ (n - 1)).map v) =
        (localPointPowerPullback c.l F.val D c.different (n - 1)).map
          ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)).map v) ≫ (localConstructibleReturnComparison c.l F.val D c.different X₀
          (localExtensionPoint D X₀ n hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x)
          M').hom) ∧
    (∀ (M M' : sfRationalConstructibleCategory c.l F.val (D.geometricFiber X₀).left)
      (v : M ⟶ M'),
      (localConstructibleReturnTransport c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x) (n - 1) (localExtensionPoint_return D X₀ n hn x) M) ≫ ((localConstructibleStalkFunctor
          c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn x)) ⋙ (pointRationalFibre D c.l
          c.different F.val)).map
          ((localGeometricPowerPullback c.l F.val D c.different X₀ (n - 1)).map v) =
        ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)) ⋙ (pointRationalFibre D c.l c.different F.val)).map v ≫
          (localConstructibleReturnTransport c.l F.val D c.different X₀ (localExtensionPoint D X₀ n
          hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x) M')) ∧
    (∀ (r : ℕ) (A B : sfWeilComplex D c.l c.different X₀ F.val) (v : A ⟶ B),
      (localWeilIterate c.l F.val D c.different X₀ A r).hom ≫ v.hom.f =
        (localGeometricPowerPullback c.l F.val D c.different X₀ r).map v.hom.f ≫ (localWeilIterate
          c.l F.val D c.different X₀ B r).hom) ∧
    (∀ (A B : sfWeilComplex D c.l c.different X₀ F.val) (v : A ⟶ B),
      (localExtensionFrobenius c.l F.val D c.different X₀ A n hn x) ≫
          ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)) ⋙ (pointRationalFibre D c.l c.different F.val)).map v.hom.f =
        ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)) ⋙ (pointRationalFibre D c.l c.different F.val)).map v.hom.f ≫ (localExtensionFrobenius
          c.l F.val D c.different X₀ B n hn x)) := by
  sorry

end WeilConjectures
