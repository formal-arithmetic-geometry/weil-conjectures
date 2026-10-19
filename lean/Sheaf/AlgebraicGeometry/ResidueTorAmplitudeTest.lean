/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Testing finite Tor amplitude at the residue field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-trace-perfectness/
`lem-exc-residue-tor-test.md` (blueprint: lem-exc-residue-tor-test).
-/

@[expose] public section

-- Keep quotient coefficient rings on the same instance path as the generic residue criterion.
-- Otherwise checking its specialization unfolds the full quotient-ring construction repeatedly.
attribute [local instance 20000] CommRing.toRing

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace Padic

/-- The residue field coefficient as an `A`-module, where `A` is the finite coefficient ring.
Source: blueprint `lem-exc-residue-tor-test` (blueprint: lem-exc-residue-tor-test). -/
noncomputable def coefficientExtensionResidueModule
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n) :=
  ModuleCat.of (Padic.coefficientExtensionRing l E n)
    ((Padic.coefficientExtensionRing l E n) ⧸
      Ideal.span ({Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionRing l E n)))

end Padic

namespace AlgebraicGeometry.Etale

-- Match the braidings used by the existing étale derived tensor construction.
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory

private theorem derivedTensor_eq_curriedTensor
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) :
    derivedTensor A T = curriedTensor (_root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  rfl

private theorem homology_bounds {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (L : _root_.DerivedCategory C) (a b : ℤ) :
    _root_.DerivedCategory.homologyConcentratedIn a b L ↔
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor C i).obj L) := by
  constructor
  · rintro ⟨hlo, hhi⟩ i (hi | hi)
    · exact (_root_.DerivedCategory.isGE_iff L a).1 hlo i hi
    · exact (_root_.DerivedCategory.isLE_iff L b).1 hhi i hi
  · intro h
    exact ⟨(_root_.DerivedCategory.isGE_iff L a).2 (fun i hi ↦ h i (.inl hi)),
      (_root_.DerivedCategory.isLE_iff L b).2 (fun i hi ↦ h i (.inr hi))⟩

private theorem residue_test
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) (r : A) (hr : IsNilpotent r)
    [(Ideal.span {r}).IsMaximal] (a b : ℤ) (K : DerivedCategoryModule A T) :
    DerivedCategory.hasTorAmplitudeIn A T a b K ↔
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
                (ModuleCat.of A (A ⧸ Ideal.span {r})))))) := by
  rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn]
  rw [derivedTensor_eq_curriedTensor (ModuleCat.{u + 1} A) T]
  refine (_root_.DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (R := A) r hr
    (Sheaf.constantSheafQuotientIsoCokernel T.smallEtaleTopology r)
    (fun F _ _ _ f _ _ hY ↦
      Sheaf.mono_whiskerRight_of_smul_id_eq_zero r f hY F) a b K).trans ?_
  exact homology_bounds _ a b

/-- Tor amplitude over `A = 𝒪_E/(ϖ_E^n)` is tested by the residue constant sheaf.

Source: Weil blueprint, smooth purity, trace perfectness, order 1823
(blueprint: lem-exc-residue-tor-test).

Proof:
1. The image r of the chosen uniformizer satisfies r^n = 0. The DVR theorem identifies
   its principal ideal in the integer ring with the maximal ideal. Mapping this ideal
   through the level-n quotient gives a maximal ideal because n is positive.
2. Apply the existing categorical residue criterion
   `DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor` to
   the category of module sheaves on the small etale site. Its two sheaf inputs are
   `Sheaf.constantSheafQuotientIsoCokernel` and
   `Sheaf.mono_whiskerRight_of_smul_id_eq_zero`. The latter uses sectionwise split
   monomorphisms of modules over the quotient field and exact sheafification.
   The categorical criterion computes tensor with a K-flat model and propagates the
   bounds along the finite filtration by powers of r using distinguished triangles.
3. The forward implication evaluates the definition at the constant residue module.
   For the converse, convert explicit vanishing to the standard t-structure bounds,
   apply the criterion, and convert its bounds back to vanishing for every test sheaf.
The bounded constructibility hypothesis is retained; the argument works for arbitrary K.
-/
theorem residue_tor_amplitude_test
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T)
    (hK : @DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn) T K) :
    DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) T a b K ↔
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero
          ((_root_.DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) i).obj
            (((derivedTensor
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf T.smallEtaleTopology
                    (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
                  (Padic.coefficientExtensionResidueModule l E n))))) := by
  have _ := hK
  have hr : (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E)) ^ n = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal := hgen ▸ hmax
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
    (m := Ideal.span {Padic.coefficientExtensionUniformizer l E})
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.pow_le_self (by omega))
  have : (Ideal.span {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E))}).IsMaximal := by
    simpa only [Ideal.map_span, Set.image_singleton] using hm
  let A := Padic.coefficientExtensionRing l E n
  let r : A := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
    (Padic.coefficientExtensionUniformizer l E)
  let K' : DerivedCategoryModule A T := K
  have hg := residue_test A T r ⟨n, hr⟩ a b K'
  exact hg

end AlgebraicGeometry.Etale
