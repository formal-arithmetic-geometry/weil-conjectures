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
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude

import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.AlgebraicGeometry.EtaleClosedSupportResidueBound

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


private theorem closed_support_boundedConstructible_torAmplitude
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ModuleCat.{u + 1} A) [Finite N]
    (htest : ∀ (S : Scheme.{u}) (x y : ℤ) (L : DerivedCategoryModule A S),
      DerivedCategory.isBoundedConstructible A S L →
      (DerivedCategory.hasTorAmplitudeIn A S x y L ↔
        ∀ q : ℤ, q < x ∨ y < q → IsZero
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            (((derivedTensor (ModuleCat.{u + 1} A) S).obj L).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N))))))
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (hc : 0 ≤ c)
    (hcd : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (hcons : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf M →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))))
    (K : DerivedCategoryModule A T)
    (hK : DerivedCategory.isBoundedConstructible A T K)
    (hTor : DerivedCategory.hasTorAmplitudeIn A T a b K) :
    DerivedCategory.isBoundedConstructible A Z
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) ∧
    DerivedCategory.hasTorAmplitudeIn A Z a (b + c + 1)
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) := by
  let Q := (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K
  obtain ⟨a₀, b₀, hab₀, hK₀⟩ := hK.2
  have hKbounds : _root_.DerivedCategory.homologyConcentratedIn a₀ b₀ K := by
    constructor
    · exact (_root_.DerivedCategory.isGE_iff K a₀).2 fun q hq ↦ hK₀ q (Or.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b₀).2 fun q hq ↦ hK₀ q (Or.inr hq)
  obtain ⟨hQbounds, hQcons⟩ :=
    (closedImmersion_rightAdjoint_amplitude A i j hij a₀ b₀ c hc hcd).2
      hcons K hKbounds hK.1
  have hQ : DerivedCategory.isBoundedConstructible A Z Q := by
    refine ⟨hQcons, a₀, b₀ + c + 1, by omega, ?_⟩
    intro q hq
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff Q a₀).1 hQbounds.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff Q (b₀ + c + 1)).1 hQbounds.2 q hq
  exact ⟨hQ, (htest Z a (b + c + 1) Q hQ).2
    (closedSupport_finiteTensor_vanishing A N i j hij a b c hc hcd K hTor)⟩

/-- Closed exceptional inverse image preserves bounded constructibility and changes
Tor amplitude [a,b] to [a,b+c+1] under the stated bounds on the complementary open image.
Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-exc-closed-tor.md,
order 1913 (blueprint: prop-exc-closed-tor).

Proof:
1. The bounded interval in bounded constructibility of K and the closed-support
   cohomology theorem give bounded constructibility of Q = Ri!K.
2. Finite cohomological dimension gives countable coproduct preservation for Rj_*.
   The residue test puts H = K tensor kappa_T in [a,b]. The cohomology clause of
   the closed-support amplitude theorem puts Ri!H in [a,b+c+1].
3. Tensor the support triangle of K by kappa_T. The open projection formula
   identifies its third term with that of the support triangle of H. The unit
   identity for the projection map proves the middle square. TR3 and the
   two-isomorphisms lemma identify the first terms.
4. Apply the monoidal closed pullback to this comparison. The fully faithful
   closed direct-image counit identifies Q tensor Li*kappa_T with Ri!H.
   Pullback of constants identifies Li*kappa_T with kappa_Z. Transport the
   cohomology bounds and apply the converse residue test to Q. -/
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
      a (b + c + 1) ((finiteCoefficientClosedExceptionalInverseImage l E n hn i).obj K) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let N := Padic.coefficientExtensionResidueModule l E n
  have : Finite N := by
    unfold N Padic.coefficientExtensionResidueModule
    exact Finite.of_surjective (Ideal.Quotient.mk _) (Ideal.Quotient.mk_surjective)
  exact closed_support_boundedConstructible_torAmplitude
    (Padic.coefficientExtensionRing l E n) N
    (residue_tor_amplitude_test l E n hn) i j _hij a b c _hc _hcd _hcons K _hK _hTor

end AlgebraicGeometry.Etale
