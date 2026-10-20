/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.InvertibleExponent

/-!
# Open direct-image constructibility on arbitrary curves

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-constructible-general.md`, statement and proof
(blueprint: thm-exc-curve-open-constructible-general).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Every higher direct image of a constructible finite prime-power-torsion module sheaf
along an open immersion into a finite-type scheme of dimension at most one over a finite
field or its algebraic closure is constructible.
Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-constructible-general.md`
(blueprint: thm-exc-curve-open-constructible-general).

Proof:
1. If T is empty, every sheaf on its small etale site is zero, hence constructible.
2. Otherwise the positive integer ell^n annihilating A is invertible on T. The proved
   `HasInvertibleExponent.of_hom_of_nonempty` descends this hypothesis to Spec k.
3. Place F in degree zero and use `boundedConstructible_singleFunctor_obj`, converting
   between the two constructibility predicates by their proved comparison. Apply
   `cor-fin-deligne-open-finite-coefficients` to obtain constructible homology in every
   degree for the ordinary derived direct image.
4. The proved `Functor.rightDerivedFunctorPlusCompatibility` identifies this with the
   bounded-below derived direct image in the statement. Transport constructibility
   along the induced homology isomorphism. -/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve
    (k : Type u) [Field k]
    (hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k)
    {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (hdim : topologicalKrullDim T ≤ 1) (j : U ⟶ T) [IsOpenImmersion j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hinv : IsUnit (ℓ : Γ(T, ⊤)))
    (hkill : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  classical
  by_cases hT : IsEmpty T
  · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _))
  have : Nonempty T := not_isEmpty_iff.mp hT
  obtain ⟨n, hn, hAn⟩ := hkill
  have : HasInvertibleExponent A T := ⟨ℓ ^ n, pow_pos hprime.pos n,
    by simpa only [nsmul_eq_mul, mul_one] using hAn,
    by simpa only [Nat.cast_pow] using hinv.pow n⟩
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := A) (T ↘ Spec (.of k))
  obtain ⟨N, hN, hAN, hunit⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := A) (X := Spec (.of k))
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  have hK' := DerivedCategory.boundedConstructible_singleFunctor_obj F 0
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK'
  have hK : DerivedCategory.isBoundedConstructible A U K := by
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb i
        (lt_of_le_of_lt (le_max_right _ _) hi)
  have hpush := isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion k A N
    ⟨hN, inferInstance, hAN, hunit⟩ (T ↘ Spec (.of k)) j K hK
  have hq := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (hpush.1 q)
  let e := (_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) j).mapIso
        ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app F))
  have : Scheme.IsConstructibleSheaf _ := hq
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (Scheme.IsConstructibleSheaf.of_iso e.symm)

end AlgebraicGeometry.Etale
