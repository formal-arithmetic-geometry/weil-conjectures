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
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.BoundedBelowConstructibleReflection
import Mathlib.Algebra.CharP.CharAndCard

set_option linter.style.haveILetI false

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
  letI : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  have hunit : IsUnit (l : D.k) := by
    letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
    letI : Fact D.p.Prime := ⟨D.prime⟩
    have hc : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    letI : CharP D.k₀ D.p := hc
    letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hlp ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : T) : D.k →+* T.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (T ↘ Spec (.of D.k)).appTop ≫ T.Γevaluation x).hom
  letI : ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  let K := (@ProEtale.finiteCoefficientIntrinsicDerivedComparison.{u} T B
    inferInstance (Padic.finite_coefficientExtensionRing l E n hn)).obj C
  have hTor' := finiteCoefficient_comparison_reflects_torAmplitude D l _hlp E n hn T a b C
    _hPlus K _hConstructible _hTor (Iso.refl K)
  exact ⟨finiteCoefficient_boundedBelow_constructible_reflection D l _hlp E n hn T C
    _hPlus _hConstructible, hTor'⟩

end AlgebraicGeometry
