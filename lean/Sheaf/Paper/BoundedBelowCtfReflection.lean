/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.IntrinsicRealizationOriginComparison
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.ComparisonTorAmplitude

/-!
# Bounded-below reflection of finite-Tor constructibility

Source: Stacks Project, Tags 099T and 09AK, and the finite-Tor comparison of the
Weil conjectures blueprint (blueprint: lem-sf-bounded-below-ctf-reflection).
This is the explicit reflection consequence for arbitrary bounded-below inputs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Site comparison reflects bounded constructibility and the specified Tor interval
for an arbitrary bounded-below étale complex, without assuming it constructible.
Source: Stacks Project, Tags 099T and 09AK; blueprint finite-Tor comparison, clause (ii)
(blueprint: lem-sf-bounded-below-ctf-reflection).

Proof:
1. By det-pe-classical-sheaves-modules, comparison on ordinary constant-coefficient
   module sheaves is exact and fully faithful. Its termwise derived functor from
   def-weil-pbc-proetale-modules therefore commutes with cohomology, since exactness
   preserves kernels, images and their quotient. Faithfulness reflects zero objects:
   if F(M) is zero, F(id_M) = F(0), hence id_M = 0.
2. The finite interval outside which the pullback cohomology vanishes is consequently
   also a vanishing interval for the original complex. This includes the zero complex.
3. For each cohomology sheaf, clause (i) of lem-sf-proetale-constructible-origin supplies
   a constructible étale antecedent of its intrinsically constructible pullback.
   Fullness lifts the isomorphism and its inverse; faithfulness makes their composites
   identities. Transport the finite stratification and finite locally constant models
   along this isomorphism. Together with step 2 this is exactly
   def-weil-pbc-constructible-complexes, without any constructibility assumption on C.
4. Apply lem-sf-comparison-tor-amplitude(ii) with K equal to the pullback of C and the
   identity isomorphism. Its antecedent is bounded below by hypothesis. The prime l is
   invertible on T because l differs from the characteristic p of D.k: its inverse in
   D.k maps to an inverse under the structure morphism. The conclusion gives étale
   Tor amplitude in the same interval [a,b], tested against every degree-zero module.
   Combine it with step 3. -/
theorem finiteCoefficient_boundedBelow_ctf_reflection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of D.k))]
    (C : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T)
    (_hPlus : _root_.DerivedCategory.TStructure.t.plus C)
    (a b : ℤ) (_hab : a ≤ b)
    (_hConstructible : Scheme.intrinsicFiniteTorsionConstructible l E n hn T
      ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj C))
    (_hTor : Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
      ((@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T
        (Padic.coefficientExtensionRing l E n) inferInstance
        (Padic.finite_coefficientExtensionRing l E n hn)).obj C) a b) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) T C ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T a b C := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  have : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  have : Finite (ULift.{u + 1, u} B) := Finite.of_equiv B Equiv.ulift.symm
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T
  let F := ProEtale.finiteCoefficientIntrinsicComparison T B
  let R := Scheme.proEtaleModuleRestriction T B
  have : R.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let H := DerivedCategory.homologyFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
  let H' := DerivedCategory.homologyFunctor
    (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B))
  let K := (ProEtale.finiteCoefficientIntrinsicDerivedComparison T B).obj C
  obtain ⟨eR⟩ := ProEtale.intrinsicRealization_restriction T B
  have eH (i : ℤ) : F.obj ((H i).obj C) ≅ (H' i).obj K :=
    (F.mapDerivedCategoryHomologyFunctorIso i).app C
  have e (i : ℤ) : ν.obj ((H i).obj C) ≅ R.obj ((H' i).obj K) :=
    (eR.app (ν.obj ((H i).obj C))).symm ≪≫ R.mapIso (eH i)
  have hfinite : Set.Finite {i : ℤ | ¬ Limits.IsZero ((H' i).obj K)} :=
    _hConstructible.1
  have hzero (i : ℤ) (hi : Limits.IsZero ((H' i).obj K)) :
      Limits.IsZero ((H i).obj C) := by
    have hz : Limits.IsZero (ν.obj ((H i).obj C)) := (R.map_isZero hi).of_iso (e i)
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply ν.map_injective
    rw [ν.map_id, ν.map_zero]
    exact hz.eq_of_src _ _
  constructor
  · constructor
    · intro i
      have hc := (Scheme.proEtaleModuleRestriction_constructible_iff T B _).mp
        (_hConstructible.2 i)
      have hc' := ProEtale.isConstructible_of_iso (e i).symm hc
      obtain ⟨G, hG, ⟨eG⟩⟩ :=
        ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
          (ULift.{u + 1, u} B) hc'
      have : Scheme.IsConstructibleSheaf G := hG
      apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      exact Scheme.IsConstructibleSheaf.of_iso (ν.preimageIso eG)
    · obtain ⟨c, hc⟩ := hfinite.bddBelow
      obtain ⟨d, hd⟩ := hfinite.bddAbove
      refine ⟨min c d, max c d, le_trans (min_le_left _ _) (le_max_left _ _), ?_⟩
      intro i hi
      apply hzero i
      by_contra hz
      rcases hi with hi | hi
      · exact (not_lt_of_ge (le_trans (min_le_left c d) (hc hz))) hi
      · exact (not_lt_of_ge (le_trans (hd hz) (le_max_right c d))) hi
  · let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hunit : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hlp.symm).isUnit
    let f := (T ↘ Spec (CommRingCat.of D.k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
    have hunitT (x : T) : IsUnit (l : T.residueField x) := by
      simpa only [map_natCast] using hunit.map
        ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ f.appTop ≫ T.Γevaluation x).hom
    let : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦ (hunitT x).invertible
    exact finiteCoefficient_comparison_reflects_torAmplitude D l _hlp E n hn T a b C
      _hPlus K _hConstructible _hTor (Iso.refl _)

end AlgebraicGeometry
