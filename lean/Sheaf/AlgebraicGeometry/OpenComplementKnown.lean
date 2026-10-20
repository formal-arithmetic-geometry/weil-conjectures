/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral
public import Sheaf.AlgebraicGeometry.CurveOpenConstructibleGeneral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete

/-!
# Open-complement bounds over an algebraic closure of a finite field

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`lem-exc-open-complement-known.md`, statement and proof
(blueprint: lem-exc-open-complement-known).

The independent dimension-zero and curve conclusions are included alongside the general bound.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact open immersion into a finite-type scheme of dimension at most `d`
over an algebraic closure of a finite field satisfies the open-complement condition with
bound `2 * d`. In dimension zero its direct image is exact extension by zero and preserves
constructibility, and the bound is zero. In dimension at most one the bound is already one.

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/lem-exc-open-complement-known.md`
(blueprint: lem-exc-open-complement-known).

Proof:
1. Algebraic closedness implies separable closedness. The prime ell is a unit in k,
   and hence in the global sections of T. A power of ell annihilating 1_A annihilates A;
   increasing its exponent gives the positive exponent required by the curve theorem.
2. A quasi-compact open immersion is finite type, so V is finite type over k.
   Its open embedding gives dim V <= dim T <= d. Clause (1) of the direct-image
   finiteness input gives constructibility in nonnegative degrees. Compare the unbounded
   and bounded-below derived direct images using rightDerivedFunctorPlusCompatibility.
   Negative cohomology vanishes; a zero sheaf is constructible.
3. The existing torsion-coefficient theorem isZero_higherDirectImage_of_two_mul_lt
   gives vanishing above 2d, since the finite additive group of A is torsion.
   Combine this with step 2 to obtain the general open-complement bound.
4. Independently, T is Noetherian. In dimension zero its underlying space is finite
   discrete, so the image of j is closed and j is a closed immersion. The canonical
   comparison from extension by zero to direct image is an isomorphism on a clopen
   immersion. Thus direct image is exact and preserves constructibility, using the
   constructibility of extension by zero and the comparison of the two definitions
   of constructible module sheaves.
5. For this exact direct image, singleFunctorCompRightDerivedFunctorIso and the
   bounded-below comparison identify its derived image of M[0] with (j_* M)[0].
   Its cohomology vanishes in every nonzero degree, while degree zero is j_* M.
   This proves both clauses of the bound zero without the general finiteness input.
6. Independently, in dimension at most one apply the stated curve vanishing and
   constructibility theorems, using the unit and positive annihilator from step 1.
   All arguments include the empty scheme and the zero coefficient ring. -/
theorem hasOpenComplementCondition_of_isAlgClosure_finite_and_lowDimension
    (k : Type u) [Field k]
    (hk : ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k)
    {T V : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)
    (hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0) :
    HasOpenComplementCondition A j (2 * d) ∧
      (topologicalKrullDim T ≤ 0 →
        IsClosedImmersion j ∧
        PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) j) ∧
        Nonempty (Etale.lowerStar (ModuleCat.{u + 1} A) j ≅
          Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j) ∧
        (∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          IsConstructibleEtaleModuleSheaf F →
            IsConstructibleEtaleModuleSheaf
              ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj F)) ∧
        HasOpenComplementCondition A j 0) ∧
      (topologicalKrullDim T ≤ 1 → HasOpenComplementCondition A j 1) := by
  have hℓk : IsUnit (ℓ : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k hprime hchar.symm).isUnit
  have hℓ : IsUnit (ℓ : Γ(T, ⊤)) := by
    simpa only [map_natCast] using hℓk.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      (T ↘ Spec (.of k)).appTop).hom
  obtain ⟨n, hn⟩ := hkill
  have hkill' : ∃ r : ℕ, 0 < r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0 := by
    refine ⟨n + 1, Nat.succ_pos _, ?_⟩
    rw [pow_succ', mul_smul, hn, smul_zero]
  have hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0 := ⟨n, hn⟩
  have halg : IsAlgClosed k := by
    obtain ⟨k₀, _, hcl⟩ := hk
    exact IsAlgClosure.isAlgClosed k₀
  have hsep : IsSepClosed k := inferInstance
  have hTnoeth : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have hTcompact : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have hVdim : topologicalKrullDim V ≤ topologicalKrullDim T :=
    j.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hA : ∀ a : A, ((ℓ ^ n : ℕ) : ℤ) • a = 0 := by
    intro a
    rw [natCast_zsmul, ← one_mul a, ← smul_mul_assoc, hn, zero_mul]
  have hN : IsUnit (((ℓ ^ n : ℕ) : ℤ) : k) := by
    simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using hℓk.pow n
  have hinput := hasDirectImageFinitenessInput_of_isSepClosed k _ hN A hA
  have hconstructible : ∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℤ), IsConstructibleEtaleModuleSheaf F →
      IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
    intro F q hF
    apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    by_cases hq : q < 0
    · exact IsConstructibleSheaf.of_isZero
        (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
          (Etale.lowerStar (ModuleCat.{u + 1} A) j) _ 0 hq)
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = m := ⟨q.toNat, by omega⟩
      have hc := hinput.1 (j ≫ (T ↘ Spec (.of k))) (T ↘ Spec (.of k)) j rfl F hF m
      have hcc : IsConstructibleSheaf
          ((DerivedCategory.homologyFunctor _ (m : ℤ)).obj
            ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
              ((DerivedCategory.singleFunctor _ 0).obj F))) :=
        (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hc
      have : IsConstructibleSheaf
          ((DerivedCategory.homologyFunctor _ (m : ℤ)).obj
            (((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor).obj
              ((DerivedCategory.Plus.ι.obj)
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := hcc
      exact IsConstructibleSheaf.of_iso
        (F := (DerivedCategory.homologyFunctor _ (m : ℤ)).obj
          ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))
        ((DerivedCategory.homologyFunctor _ (m : ℤ)).mapIso
          ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm
  have hgeneral : HasOpenComplementCondition A j (2 * d) := by
    refine ⟨?_, hconstructible⟩
    intro M q hq
    exact Etale.isZero_higherDirectImage_of_two_mul_lt
      (isAddTorsion_of_finite : IsAddTorsion A) j
      (j ≫ (T ↘ Spec (.of k))) (T ↘ Spec (.of k)) rfl d (hVdim.trans hdim) M q
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq)
  refine ⟨hgeneral, ?_, ?_⟩
  · intro hdim0
    have hdiscrete := finite_and_discreteTopology_of_topologicalKrullDim_le_zero T hdim0
    have : DiscreteTopology T := hdiscrete.2
    have hjclosed : IsClosed (Set.range j) := isClosed_discrete _
    have hj : IsClosedImmersion j := IsClosedImmersion.of_isPreimmersion j hjclosed
    have he := Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
      (ModuleCat.{u + 1} A) j hjclosed
    obtain ⟨e⟩ : Nonempty (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j ≅
        Etale.lowerStar (ModuleCat.{u + 1} A) j) :=
      ⟨asIso (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j)⟩
    have hexact : PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) j) :=
      preservesFiniteColimits_of_natIso e
    have hpush : ∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
        IsConstructibleEtaleModuleSheaf F →
        IsConstructibleEtaleModuleSheaf
          ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj F) := by
      intro F hF
      have : IsConstructibleSheaf F :=
        (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
      have : IsConstructibleSheaf
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) :=
        IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact j F
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
        (IsConstructibleSheaf.of_iso (e.app F))
    have hsingle (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
        Nonempty ((DerivedCategory.Plus.ι.obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) ≅
          (DerivedCategory.singleFunctor _ 0).obj
            ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj M)) :=
      ⟨((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≪≫
      ((Etale.lowerStar (ModuleCat.{u + 1} A) j).singleFunctorCompRightDerivedFunctorIso.app M)⟩
    have hvan : ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
        (q : ℤ), q ≠ 0 → IsZero
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
      intro M q hq
      obtain ⟨eM⟩ := hsingle M
      refine IsZero.of_iso ?_
        ((DerivedCategory.homologyFunctor _ q).mapIso eM)
      rcases lt_or_gt_of_ne hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ 0 q hq
      · exact DerivedCategory.isZero_of_isLE _ 0 q hq
    refine ⟨hj, hexact, ⟨e.symm⟩, hpush, ?_⟩
    refine ⟨fun M q hq ↦ hvan M q (by omega), ?_⟩
    intro F q hF
    apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    by_cases hq : q = 0
    · subst q
      obtain ⟨eF⟩ := hsingle F
      have : IsConstructibleSheaf
          ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj F) :=
        (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hpush F hF)
      exact IsConstructibleSheaf.of_iso
        (F := (Etale.lowerStar (ModuleCat.{u + 1} A) j).obj F)
        (((DerivedCategory.homologyFunctor _ 0).mapIso eF) ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
    · exact IsConstructibleSheaf.of_isZero (hvan F q hq)
  · intro hdim1
    refine ⟨?_, ?_⟩
    · intro M q hq
      exact AlgebraicGeometry.Etale.isZero_higherDirectImage_of_open_curve k
        (Or.inr hk) hdim1 j A ℓ hprime hℓ hkill M q hq
    · intro F q hF
      exact AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve
        k (Or.inr hk) hdim1 j A ℓ hprime hℓ hkill' F hF q

end AlgebraicGeometry.Scheme
