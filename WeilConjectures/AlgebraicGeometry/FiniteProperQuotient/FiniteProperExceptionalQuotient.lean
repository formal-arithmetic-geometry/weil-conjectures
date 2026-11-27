/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.OrdinaryExceptionalCtfPreservation
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement

import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Finite proper exceptional inverse image and quotient coefficients

Indices `n : ℕ` denote the positive exponents `n + 1`. All categories are ordinary
unbounded small-etale derived categories. Only their ctf object predicates are restricted.

## References

* Zheng, Propositions 2.29(2) and 3.16(2)
* Stacks Project, Tags 06YY, 03RW, 09AL, 03EK
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteProperQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient by the indicated power of ell, rather than a uniformizer power. -/
abbrev Ring (n : ℕ) :=
  Padic.coefficientExtensionEllQuotient l E (n + 1)

/-- The quotient homomorphism induced by the identity of the ring of integers. -/
def quotient {m n : ℕ} (h : n ≤ m) : Ring l E m →+* Ring l E n :=
  Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.add_le_add_right h 1)))

/-- Derived quotient tensor on the ambient ordinary etale category. -/
abbrev Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  scalarExtension (quotient l E h) T

/-- The ordinary, unbounded derived direct image with this finite coefficient ring. -/
abbrev F {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :=
  R(lowerStar (ModuleCat.{u + 1} (Ring l E n)) p)

/-- The existing bounded constructible finite-Tor predicate. For the Noetherian schemes
of this theorem, its finite stratification condition is equivalent to affine-local
constructibility. -/
abbrev Ctf (T : Scheme.{u}) (n : ℕ) :=
  DerivedCategory.boundedConstructibleFiniteTor (Ring l E n) T

/-- Canonical tensor reassociation: conjugate the sectionwise restriction comparison. -/
def reassoc (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n) :
    Q l E T h ⋙ Q l E T ht ≅ Q l E T (ht.trans h) :=
  Adjunction.leftAdjointCompIso
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E h)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E ht)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E (ht.trans h))))
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology
      (RingHom.ext fun x ↦ Quotient.inductionOn x fun _ ↦ rfl))

/-- The sectionwise identity restriction at an equal-index quotient. -/
def restrictionSelf (T : Scheme.{u}) (n : ℕ) :
    Sheaf.restrictScalars T.smallEtaleTopology (quotient l E (le_refl n)) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ (fullyFaithfulSheafToPresheaf T.smallEtaleTopology _).preimageIso
      (Functor.isoWhiskerLeft M.obj
        (ModuleCat.restrictScalarsId' (quotient l E (le_refl n))
          (RingHom.ext fun x ↦ Quotient.inductionOn x fun _ ↦ rfl))))
    (fun {_ _} f ↦ by ext U x; rfl)

/-- The tensor identity comparison, fixed by the scalar adjunction. -/
def selfReduction (T : Scheme.{u}) (n : ℕ) : Q l E T (le_refl n) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E (le_refl n))))
    (Adjunction.id : 𝟭 (DerivedCategoryModule (Ring l E n) T) ⊣ 𝟭 _)).symm
      (Functor.mapDerivedCategoryNatIso (restrictionSelf l E T n) ≪≫
        Functor.mapDerivedCategoryIdIso _)).symm

theorem exists_span_pow_eq_coefficientExtensionIdeal (r : ℕ) :
    ∃ k : ℕ, Ideal.span ({(l : Padic.coefficientExtensionIntegers l E) ^ r} :
      Set (Padic.coefficientExtensionIntegers l E)) = Padic.coefficientExtensionIdeal l E k := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) := h.2.2.2.2.2.2.2.1
  have hgen := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hirr : Irreducible (Padic.coefficientExtensionUniformizer l E) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalRing.eq_maximalIdeal h.2.2.2.2.1]
    exact hgen.symm
  have hl : ((l : Padic.coefficientExtensionIntegers l E) ^ r) ≠ 0 := by
    refine pow_ne_zero _ fun h0 ↦ ?_
    have h1 := congrArg (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) h0
    simp only [Subring.coe_natCast, ZeroMemClass.coe_zero] at h1
    have h2 : algebraMap ℚ_[l] E (l : ℚ_[l]) = 0 := by simpa using h1
    have h3 := (FaithfulSMul.algebraMap_injective ℚ_[l] E) (h2.trans (map_zero _).symm)
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h3
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(l : Padic.coefficientExtensionIntegers l E) ^ r})
    (by simpa [Ideal.span_singleton_eq_bot] using hl) hirr
  exact ⟨k, by rw [hk, Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]⟩

instance finite_ring (n : ℕ) : Finite (Ring l E n) := by
  obtain ⟨k, hk⟩ := exists_span_pow_eq_coefficientExtensionIdeal l E (n + 1)
  exact @Finite.of_surjective _ _
    (Padic.finite_coefficientExtensionRing l E (k + 1) (Nat.le_add_left 1 k))
    ((Ideal.quotEquivOfEq hk.symm) ∘
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k)))
    ((Ideal.quotEquivOfEq hk.symm).surjective.comp (Ideal.Quotient.factor_surjective _))

theorem natCast_pow_eq_zero (n : ℕ) : ((l ^ (n + 1) : ℕ) : Ring l E n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.subset_span rfl

theorem isUnit_natCast (n : ℕ) (p₀ : ℕ) [Fact p₀.Prime] (h : l ≠ p₀) :
    IsUnit (p₀ : Ring l E n) := by
  have hc : Nat.Coprime p₀ (l ^ (n + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out Fact.out).2 (Ne.symm h))
  have hb := Nat.gcd_eq_gcd_ab p₀ (l ^ (n + 1))
  rw [hc] at hb
  have hR := congrArg (Int.cast : ℤ → Ring l E n) hb
  push_cast at hR
  have h0 : (l : Ring l E n) ^ (n + 1) = 0 := by exact_mod_cast natCast_pow_eq_zero l E n
  exact IsUnit.of_mul_eq_one ((p₀.gcdA (l ^ (n + 1)) : ℤ) : Ring l E n)
    (by linear_combination -hR - ((p₀.gcdB (l ^ (n + 1)) : ℤ) : Ring l E n) * h0)

theorem ctf_of_adjunction {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (G : DerivedCategoryModule (Ring l E n) Y ⥤ DerivedCategoryModule (Ring l E n) Z)
    (adj : F l E p n ⊣ G)
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀] (hl : l ≠ p₀)
    [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsProper p]
    (L : DerivedCategoryModule (Ring l E n) Y) (hL : Ctf l E Y n L) :
    Ctf l E Z n (G.obj L) := by
  let : Invertible (p₀ : Ring l E n) := (isUnit_natCast l E n p₀ hl).invertible
  have : HasInvertibleExponent (Ring l E n) (Spec (.of k)) :=
    HasInvertibleExponent.spec_of_charP _ p₀
  have : HasInvertibleExponent (Ring l E n) Y := .of_hom (Y ↘ Spec (.of k))
  let e : G ≅ R(p)^![Ring l E n] := adj.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction (Ring l E n) p).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ p))
  have h := constructibleFiniteTor_rightDerivedUpperShriek (Ring l E n) (Y ↘ Spec (.of k)) p hL
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring l E n)) Z).prop_of_iso
    (e.app L).symm h

/-- Tower coherence of scalar mates. -/
theorem scalarMate_quotient_trans {Z Y : Scheme.{u}} (p : Z ⟶ Y) {m n t : ℕ} (h : n ≤ m)
    (ht : t ≤ n) (K : DerivedCategoryModule (Ring l E m) Z) :
    (Q l E Y ht).map ((scalarMate (quotient l E h) p).app K) ≫
        (scalarMate (quotient l E ht) p).app ((Q l E Z h).obj K) ≫
        (F l E p t).map ((reassoc l E Z h ht).hom.app K) =
      (reassoc l E Y h ht).hom.app ((F l E p m).obj K) ≫
        (scalarMate (quotient l E (ht.trans h)) p).app K := by
  sorry

/-- Identity coherence of scalar mates. -/
theorem scalarMate_quotient_refl {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (K : DerivedCategoryModule (Ring l E n) Z) :
    (scalarMate (quotient l E (le_refl n)) p).app K ≫
        (F l E p n).map ((selfReduction l E Z n).hom.app K) =
      (selfReduction l E Y n).hom.app ((F l E p n).obj K) := by
  sorry

section
variable {Cm Cn Ct Dm Dn Dt : Type*} [Category Cm] [Category Cn] [Category Ct]
  [Category Dm] [Category Dn] [Category Dt]
  {Fm : Cm ⥤ Dm} {Gm : Dm ⥤ Cm} {Fn : Cn ⥤ Dn} {Gn : Dn ⥤ Cn} {Ft : Ct ⥤ Dt} {Gt : Dt ⥤ Ct}
  (am : Fm ⊣ Gm) (an : Fn ⊣ Gn) (at' : Ft ⊣ Gt)
  {QZh : Cm ⥤ Cn} {QYh : Dm ⥤ Dn} {QZht : Cn ⥤ Ct} {QYht : Dn ⥤ Dt}
  {QZc : Cm ⥤ Ct} {QYc : Dm ⥤ Dt}

private theorem mateEquiv_inv_trans (qh : Fm ⋙ QYh ≅ QZh ⋙ Fn) (qht : Fn ⋙ QYht ≅ QZht ⋙ Ft)
    (qc : Fm ⋙ QYc ≅ QZc ⋙ Ft) (rZ : QZh ⋙ QZht ≅ QZc) (rY : QYh ⋙ QYht ≅ QYc)
    (hq : ∀ K, QYht.map (qh.hom.app K) ≫ qht.hom.app (QZh.obj K) ≫ Ft.map (rZ.hom.app K) =
      rY.hom.app (Fm.obj K) ≫ qc.hom.app K) (L : Dm) :
    QZht.map ((mateEquiv am an (.mk _ _ _ _ qh.inv)).app L) ≫
        (mateEquiv an at' (.mk _ _ _ _ qht.inv)).app (QYh.obj L) ≫ Gt.map (rY.hom.app L) =
      rZ.hom.app (Gm.obj L) ≫ (mateEquiv am at' (.mk _ _ _ _ qc.inv)).app L := by
  apply (at'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have c1 := mateEquiv_counit an at' (.mk _ _ _ _ qht.inv) (QYh.obj L)
  have c2 := mateEquiv_counit am an (.mk _ _ _ _ qh.inv) L
  have c3 := mateEquiv_counit am at' (.mk _ _ _ _ qc.inv) L
  dsimp only [TwoSquare.mk, Functor.comp_obj] at c1 c2 c3
  rw [at'.counit_naturality, reassoc_of% c1, c3]
  have hn := qht.inv.naturality ((mateEquiv am an (.mk _ _ _ _ qh.inv)).app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn, ← QYht.map_comp_assoc, c2, QYht.map_comp_assoc]
  have hr := rY.hom.naturality (am.counit.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hr
  rw [hr]
  have h := hq (Gm.obj L)
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [← cancel_mono (qc.hom.app (Gm.obj L))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← h, ← QYht.map_comp_assoc]
  simp

private theorem mateEquiv_inv_refl {F : Cm ⥤ Dm} {G : Dm ⥤ Cm} (a : F ⊣ G) {QZ : Cm ⥤ Cm}
    {QY : Dm ⥤ Dm} (q : F ⋙ QY ≅ QZ ⋙ F) (sZ : QZ ≅ 𝟭 Cm) (sY : QY ≅ 𝟭 Dm)
    (hq : ∀ K, q.hom.app K ≫ F.map (sZ.hom.app K) = sY.hom.app (F.obj K)) (L : Dm) :
    (mateEquiv a a (.mk _ _ _ _ q.inv)).app L ≫ G.map (sY.hom.app L) = sZ.hom.app (G.obj L) := by
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have c := mateEquiv_counit a a (.mk _ _ _ _ q.inv) L
  dsimp only [TwoSquare.mk, Functor.comp_obj] at c
  rw [a.counit_naturality, reassoc_of% c]
  have hs := sY.hom.naturality (a.counit.app L)
  dsimp only [Functor.id_map, Functor.id_obj] at hs
  rw [hs, ← Category.assoc]
  congr 1
  dsimp only [Functor.comp_obj]
  rw [← hq]
  simp

end
variable {Z Y : Scheme.{u}} (p : Z ⟶ Y)
  (G : ∀ n : ℕ, DerivedCategoryModule (Ring l E n) Y ⥤
    DerivedCategoryModule (Ring l E n) Z)
  (adj : ∀ n : ℕ, F l E p n ⊣ G n)

/-- The right-adjoint mate of the inverse of the canonical proper comparison. -/
def b {m n : ℕ} (h : n ≤ m)
    (q : F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n) :
    G m ⋙ Q l E Z h ⟶ Q l E Y h ⋙ G n :=
  (mateEquiv (adj m) (adj n) (.mk _ _ _ _ q.inv))

/-- Exceptional quotient mate iso on ctf. -/
theorem isIso_b_app {m n : ℕ} (h : n ≤ m)
    (q : F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n)
    (hq : q.hom = scalarMate (quotient l E h) p)
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀] (_hl : l ≠ p₀)
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [IsProper p]
    (L : DerivedCategoryModule (Ring l E m) Y) (hL : Ctf l E Y m L) :
    IsIso ((b l E p G adj h q).app L) := by
  sorry

include G adj in
/-- Ordinary proper exceptional inverse images preserve ctf and have coherent quotient mates.
-/
theorem finite_proper_exceptional_quotient
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀] (_hl : l ≠ p₀)
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ (n : ℕ) (L : DerivedCategoryModule (Ring l E n) Y),
      Ctf l E Y n L → Ctf l E Z n ((G n).obj L)) ∧
    ∃ q : ∀ {m n : ℕ} (h : n ≤ m),
        F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n,
      (∀ {m n : ℕ} (h : n ≤ m), (q h).hom = scalarMate (quotient l E h) p) ∧
      (∀ {m n : ℕ} (h : n ≤ m) (L : DerivedCategoryModule (Ring l E m) Y),
        Ctf l E Y m L → IsIso ((b l E p G adj h (q h)).app L)) ∧
      (∀ {m n : ℕ} (h : n ≤ m) (L : DerivedCategoryModule (Ring l E m) Y),
        Ctf l E Y m L →
        (q h).hom.app ((G m).obj L) ≫
          (F l E p n).map ((b l E p G adj h (q h)).app L) ≫
          (adj n).counit.app ((Q l E Y h).obj L) =
        (Q l E Y h).map ((adj m).counit.app L)) ∧
      (∀ {m n : ℕ} (h : n ≤ m) (K : DerivedCategoryModule (Ring l E m) Z),
        Ctf l E Z m K → Ctf l E Y m ((F l E p m).obj K) →
        (Q l E Z h).map ((adj m).unit.app K) ≫
          (b l E p G adj h (q h)).app ((F l E p m).obj K) ≫
          (G n).map ((q h).hom.app K) = (adj n).unit.app ((Q l E Z h).obj K)) ∧
      (∀ {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n)
          (L : DerivedCategoryModule (Ring l E m) Y), Ctf l E Y m L →
        (Q l E Z ht).map ((b l E p G adj h (q h)).app L) ≫
          (b l E p G adj ht (q ht)).app ((Q l E Y h).obj L) ≫
          (G t).map ((reassoc l E Y h ht).hom.app L) =
        (reassoc l E Z h ht).hom.app ((G m).obj L) ≫
          (b l E p G adj (ht.trans h) (q (ht.trans h))).app L) ∧
      (∀ (n : ℕ) (L : DerivedCategoryModule (Ring l E n) Y), Ctf l E Y n L →
        (b l E p G adj (le_refl n) (q (le_refl n))).app L ≫
          (G n).map ((selfReduction l E Y n).hom.app L) =
        (selfReduction l E Z n).hom.app ((G n).obj L)) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (Z ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have hiso {m n : ℕ} (h : n ≤ m) : IsIso (scalarMate (quotient l E h) p) := by
    have := fun K ↦ (properFiniteCoefficientExtension (quotient l E h) p).1 K
    exact NatIso.isIso_of_isIso_app _
  let q {m n : ℕ} (h : n ≤ m) : F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n :=
    @asIso _ _ _ _ _ (hiso h)
  -- counit characterisation of `b`
  have hcounit {m n : ℕ} (h : n ≤ m) (L : DerivedCategoryModule (Ring l E m) Y) :
      (F l E p n).map ((b l E p G adj h (q h)).app L) ≫ (adj n).counit.app ((Q l E Y h).obj L) =
        (q h).inv.app ((G m).obj L) ≫ (Q l E Y h).map ((adj m).counit.app L) :=
    mateEquiv_counit (adj m) (adj n) (TwoSquare.mk _ _ _ _ (q h).inv) L
  refine ⟨fun n L hL ↦ ctf_of_adjunction l E p n (G n) (adj n) p₀ k _hl L hL, @q,
    fun h ↦ rfl, fun h L hL ↦ isIso_b_app l E p G adj h (q h) rfl p₀ k _hl L hL,
    fun h L _ ↦ ?_, fun h K _ _ ↦ ?_, fun h ht L _ ↦ ?_, fun n L _ ↦ ?_⟩
  · rw [hcounit, Iso.hom_inv_id_app_assoc]
  · have hu := unit_mateEquiv (adj _) (adj _) (TwoSquare.mk _ _ _ _ (q h).inv) K
    change (Q l E Z h).map ((adj _).unit.app K) ≫ (b l E p G adj h (q h)).app _ =
      (adj _).unit.app _ ≫ (G _).map ((q h).inv.app K) at hu
    rw [reassoc_of% hu, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · exact mateEquiv_inv_trans (adj _) (adj _) (adj _) (q h) (q ht) (q (ht.trans h))
      (reassoc l E Z h ht) (reassoc l E Y h ht)
      (fun K ↦ scalarMate_quotient_trans l E p h ht K) L
  · exact mateEquiv_inv_refl (adj n) (q (le_refl n)) (selfReduction l E Z n)
      (selfReduction l E Y n) (fun K ↦ scalarMate_quotient_refl l E p n K) L


end AlgebraicGeometry.Etale.FiniteProperQuotient
