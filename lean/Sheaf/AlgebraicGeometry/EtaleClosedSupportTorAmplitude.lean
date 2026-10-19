/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import Sheaf.Paper.EtaleKFlatCriteria
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ExceptionalConstantTensor
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact

/-!
# Finite Tor amplitude for closed support

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-a1-kummer,
prop-exc-closed-tor, order 1913 (blueprint: prop-exc-closed-tor).

The coefficients are the recorded quotient of the integer ring of a finite p-adic
extension. The exceptional inverse image is the ambient right adjoint supplied by
lem-exc-closed-ambient. Constructibility uses the recorded finite-value stratifications.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The ambient closed exceptional inverse image for the recorded finite coefficient ring.
It is the chosen right adjoint to the actual unbounded derived closed direct image.
Only the finiteness proof from def-weil-l-adic-coefficient-extension is installed;
the adjoint is determined by its universal property, as in lem-exc-closed-ambient.
Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-exc-closed-tor.md,
coefficient and ambient-adjoint conventions (blueprint: prop-exc-closed-tor). -/
noncomputable def finiteCoefficientClosedExceptionalInverseImage
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T ⥤
      DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Z :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  (R(lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) i)).rightAdjoint

/-- Closed exceptional inverse image preserves bounded constructibility and changes
Tor amplitude [a,b] to [a,b+c+1] under the stated bounds on the complementary open image.
Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-exc-closed-tor.md,
order 1913 (blueprint: prop-exc-closed-tor).

Proof (the seven steps of the node):
1. The open immersion is quasi-separated since its diagonal is an isomorphism.
   The coefficient ring is finite (def-weil-l-adic-coefficient-extension), so
   lem-exc-direct-image-coproducts gives all coproducts, including countable ones, for Rj_*.
2. Set Q = Ri^! K and d = b+c+1. Testing Tor amplitude on the tensor unit gives
   cohomology of K in [a,b] (def-kun-tor-amplitude). If a>b, K and Q are zero.
   Otherwise lem-exc-closed-amplitude makes Q bounded constructible in [a,d].
3. For kappa = A/(varpi), successively resolve kappa by finite free A-modules in
   nonpositive degrees; all successive kernels are finite. Constant sheaves preserve
   this resolution (lem-constructible-constant-exact). Its terms are flat and the
   complex is K-flat (lem-kun-kflat-criteria), computing def-kun-derived-tensor.
4. Closed direct image is exact (lemma-weil-pbc-finite-direct-image-exact), and its
   stalk is the original stalk on Z and zero off Z (lemma-weil-pbc-finite-stalk-formula).
   Exact conservative geometric stalks (prop-weil-pbc-geometric-stalks-exact and
   lemma-weil-pbc-geometric-stalk-conservative) detect cohomology bounds. Represent
   the bounded Q by a bounded complex L. Tensor L with the resolution in step 3.
   Every total degree has finitely many summands. Since i_* is additive and A-linear,
   it commutes with those sums, the finite free terms, and the differential matrices.
   Thus i_*(Q tensor^L kappa_Z) is (i_* Q) tensor^L kappa_T.
5. Tensor the support triangle (lem-exc-closed-support-triangle) with kappa_T, using
   lem-kun-derived-tensor-triangulated. Step 4 identifies its first term. Step 1 and
   lem-exc-constant-tensor identify its third term with Rj_* j^*(K tensor^L kappa_T).
   The middle arrow is the unit: its adjoint is the identity by
   def-kun-projection-formula-map and the adjunction triangle identity. Rotate and
   apply TR3 (def-weil-triangulated-category) to compare with the support triangle
   of H = K tensor^L kappa_T. The third map is invertible by
   lem-sf-triangle-morphism-iso. Shifting back identifies the closed images of
   Q tensor^L kappa_Z and Ri^! H, with coefficient ring A throughout.
6. The forward lem-exc-residue-tor-test gives H in [a,b]. Apply only the cohomology
   clause of lem-exc-closed-amplitude to H, obtaining Ri^! H in [a,d]. Step 5 and
   exactness and detection of bounds in step 4 give Q tensor^L kappa_Z in [a,d].
   No constructibility hypothesis on H is needed.
7. Q is bounded constructible by step 2. The converse lem-exc-residue-tor-test on Z,
   applied with step 6, gives its Tor amplitude in [a,d]. -/
theorem closedImmersion_rightAdjoint_torAmplitude
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (_hc : 0 ≤ c)
    (_hcd : ∀ (M : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (_hcons : ∀ (M : Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (q : ℤ),
      @Scheme.IsConstructibleEtaleModuleSheaf U (Padic.coefficientExtensionRing l E n)
        inferInstance (Padic.finite_coefficientExtensionRing l E n hn) M →
      @Scheme.IsConstructibleEtaleModuleSheaf T (Padic.coefficientExtensionRing l E n)
        inferInstance (Padic.finite_coefficientExtensionRing l E n hn)
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T)
    (_hK : @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      inferInstance (Padic.finite_coefficientExtensionRing l E n hn) T K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n)
      T a b K) :
    @DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n)
      inferInstance (Padic.finite_coefficientExtensionRing l E n hn) Z
      ((finiteCoefficientClosedExceptionalInverseImage l E n hn i).obj K) ∧
    DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Z
      a (b + c + 1) ((finiteCoefficientClosedExceptionalInverseImage l E n hn i).obj K) := sorry

end AlgebraicGeometry.Etale
