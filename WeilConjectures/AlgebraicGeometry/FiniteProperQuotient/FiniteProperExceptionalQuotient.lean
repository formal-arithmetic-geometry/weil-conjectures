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
import WeilConjectures.AlgebraicGeometry.OrdinaryExceptionalScalarCoefficientPullback
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarMateRestrictionTranspose
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareCube
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Finite proper exceptional inverse image and quotient coefficients

Indices `n : ℕ` denote the positive exponents `n + 1`. All categories are ordinary
unbounded small-etale derived categories. Only their ctf object predicates are restricted.

## Implementation details

The coherence of the scalar mates `scalarMate` with composite and identity quotients is
transposed, along restriction of scalars and then along the derived inverse image, to the
underived compatibility of `upperStarRestrictScalarsIsoSheaf` with restriction of scalars.
The formal mate pastings are proved for arbitrary categories and then instantiated.

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

/-- The ideal generated by a power of `ℓ` in the ring of integers is a power of the
maximal ideal. -/
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

/-- The positive `ℓ`-power quotients of the ring of integers are finite rings. -/
instance finite_ring (n : ℕ) : Finite (Ring l E n) := by
  obtain ⟨k, hk⟩ := exists_span_pow_eq_coefficientExtensionIdeal l E (n + 1)
  exact @Finite.of_surjective _ _
    (Padic.finite_coefficientExtensionRing l E (k + 1) (Nat.le_add_left 1 k))
    ((Ideal.quotEquivOfEq hk.symm) ∘
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k)))
    ((Ideal.quotEquivOfEq hk.symm).surjective.comp (Ideal.Quotient.factor_surjective _))

/-- The exponent `ℓ ^ (n + 1)` vanishes in the quotient ring. -/
theorem natCast_pow_eq_zero (n : ℕ) : ((l ^ (n + 1) : ℕ) : Ring l E n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.subset_span rfl

/-- A prime different from `ℓ` is a unit in the quotient ring. -/
theorem isUnit_natCast_of_ne (n : ℕ) (p₀ : ℕ) [Fact p₀.Prime] (h : l ≠ p₀) :
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

/-- For a proper morphism `p` of finite type schemes over a field of characteristic
`p₀ ≠ ℓ`, every right adjoint of the derived direct image `Rp_*` preserves ctf objects. -/
theorem ctf_obj_of_adjunction {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (G : DerivedCategoryModule (Ring l E n) Y ⥤ DerivedCategoryModule (Ring l E n) Z)
    (adj : F l E p n ⊣ G)
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀] (hl : l ≠ p₀)
    [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsProper p]
    (L : DerivedCategoryModule (Ring l E n) Y) (hL : Ctf l E Y n L) :
    Ctf l E Z n (G.obj L) := by
  let : Invertible (p₀ : Ring l E n) := (isUnit_natCast_of_ne l E n p₀ hl).invertible
  have : HasInvertibleExponent (Ring l E n) (Spec (.of k)) :=
    HasInvertibleExponent.spec_of_charP _ p₀
  have : HasInvertibleExponent (Ring l E n) Y := .of_hom (Y ↘ Spec (.of k))
  let e : G ≅ R(p)^![Ring l E n] := adj.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction (Ring l E n) p).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ p))
  have h := constructibleFiniteTor_rightDerivedUpperShriek (Ring l E n) (Y ↘ Spec (.of k)) p hL
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring l E n)) Z).prop_of_iso
    (e.app L).symm h

section MatePasting

variable {Cm Cn Ct Dm Dn Dt : Type*} [Category Cm] [Category Cn] [Category Ct]
  [Category Dm] [Category Dn] [Category Dt]
  {Fm : Cm ⥤ Dm} {Gm : Dm ⥤ Cm} {Fn : Cn ⥤ Dn} {Gn : Dn ⥤ Cn}
  {Ft : Ct ⥤ Dt} {Gt : Dt ⥤ Ct}
  {QZh : Cm ⥤ Cn} {QYh : Dm ⥤ Dn} {QZht : Cn ⥤ Ct} {QYht : Dn ⥤ Dt}
  {QZc : Cm ⥤ Ct} {QYc : Dm ⥤ Dt}

private theorem mateEquiv_inv_trans (am : Fm ⊣ Gm) (an : Fn ⊣ Gn) (at' : Ft ⊣ Gt)
    (qh : Fm ⋙ QYh ≅ QZh ⋙ Fn) (qht : Fn ⋙ QYht ≅ QZht ⋙ Ft)
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


private theorem mate_refl_of_transpose {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {QC : C ⥤ C} {QD : D ⥤ D} {resC : C ⥤ C}
    {resD : D ⥤ D} (aC : QC ⊣ resC) (aD : QD ⊣ resD) (α : F ⋙ QD ⟶ QC ⋙ F)
    (δ : resC ⋙ F ≅ F ⋙ resD) (hδ : mateEquiv aC aD (.mk _ _ _ _ α) = δ.hom)
    (sC : QC ≅ 𝟭 C) (sD : QD ≅ 𝟭 D) (ρC : resC ≅ 𝟭 C) (ρD : resD ≅ 𝟭 D)
    (hsC : ∀ K, aC.unit.app K ≫ ρC.hom.app (QC.obj K) = sC.inv.app K)
    (hsD : ∀ K, aD.unit.app K ≫ ρD.hom.app (QD.obj K) = sD.inv.app K)
    (h : ∀ K, δ.inv.app K ≫ F.map (ρC.hom.app K) = ρD.hom.app (F.obj K)) (K : C) :
    α.app K ≫ F.map (sC.hom.app K) = sD.hom.app (F.obj K) := by
  have hC (K : C) : aC.unit.app K ≫ resC.map (sC.hom.app K) = ρC.inv.app K := by
    have u' : aC.unit.app K = sC.inv.app K ≫ ρC.inv.app (QC.obj K) := by
      rw [← hsC]; simp
    rw [u', Category.assoc]
    have := ρC.inv.naturality (sC.hom.app K)
    dsimp only [Functor.id_map, Functor.id_obj] at this
    rw [← this, ← Category.assoc]
    simp
  have hD (K : D) : aD.unit.app K ≫ resD.map (sD.hom.app K) = ρD.inv.app K := by
    have u' : aD.unit.app K = sD.inv.app K ≫ ρD.inv.app (QD.obj K) := by
      rw [← hsD]; simp
    rw [u', Category.assoc]
    have := ρD.inv.naturality (sD.hom.app K)
    dsimp only [Functor.id_map, Functor.id_obj] at this
    rw [← this, ← Category.assoc]
    simp
  apply (aD.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hD, Functor.map_comp]
  have u := unit_mateEquiv aC aD (.mk _ _ _ _ α) K
  rw [hδ] at u
  dsimp only [TwoSquare.mk, Functor.comp_obj] at u
  rw [← reassoc_of% u]
  have n := δ.hom.naturality (sC.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n
  rw [← n, ← F.map_comp_assoc, hC, ← cancel_mono (ρD.hom.app (F.obj K)), ← h K]
  simp only [Functor.id_obj, Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app_map]
  rw [h K, Iso.inv_hom_id_app]
  rfl

private theorem whiskered_square_unitors {C D : Type*} [Category C] [Category D] {U u : C ⥤ D}
    {resC : C ⥤ C} {resD : D ⥤ D}
    (ldu : U ≅ u) (sq : resC ⋙ u ≅ u ⋙ resD) (ρC : resC ≅ 𝟭 C) (ρD : resD ≅ 𝟭 D)
    (h : ∀ M, sq.hom.app M ≫ ρD.hom.app (u.obj M) = u.map (ρC.hom.app M)) (M : C) :
    (Functor.isoWhiskerLeft resC ldu ≪≫ sq ≪≫ Functor.isoWhiskerRight ldu.symm resD).hom.app M ≫
        ρD.hom.app (U.obj M) = U.map (ρC.hom.app M) := by
  have n := ρD.hom.naturality (ldu.inv.app M)
  dsimp only [Functor.id_map, Functor.id_obj] at n
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, Functor.comp_obj]
  rw [n, reassoc_of% (h M)]
  have n' := ldu.hom.naturality (ρC.hom.app M)
  dsimp only [Functor.id_obj] at n'
  rw [← reassoc_of% n', Iso.hom_inv_id_app, Category.comp_id]

private theorem mate_refl_of_square {C D : Type*} [Category C] [Category D] {U : C ⥤ D}
    {F : D ⥤ C} (adj : U ⊣ F) {resC : C ⥤ C}
    {resD : D ⥤ D} (σ : resC ⋙ U ⟶ U ⋙ resD) (ρC : resC ≅ 𝟭 C) (ρD : resD ≅ 𝟭 D)
    (h : ∀ M, σ.app M ≫ ρD.hom.app (U.obj M) = U.map (ρC.hom.app M)) (K : D) :
    (mateEquiv adj adj (.mk _ _ _ _ σ)).app K ≫ F.map (ρD.hom.app K) =
      ρC.hom.app (F.obj K) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have c := mateEquiv_counit adj adj (.mk _ _ _ _ σ) K
  dsimp only [TwoSquare.mk, Functor.comp_obj] at c
  rw [adj.counit_naturality, reassoc_of% c]
  have n := ρD.hom.naturality (adj.counit.app K)
  dsimp only [Functor.id_map, Functor.id_obj] at n
  rw [n, ← Category.assoc]
  exact congrArg (· ≫ adj.counit.app K) (h (F.obj K))

private theorem mate_trans_of_transpose {Fm : Cm ⥤ Dm} {Fn : Cn ⥤ Dn} {Ft : Ct ⥤ Dt}
    {QZh : Cm ⥤ Cn} {QZht : Cn ⥤ Ct} {QZc : Cm ⥤ Ct}
    {QYh : Dm ⥤ Dn} {QYht : Dn ⥤ Dt} {QYc : Dm ⥤ Dt}
    {resZh : Cn ⥤ Cm} {resZht : Ct ⥤ Cn} {resZc : Ct ⥤ Cm}
    {resYh : Dn ⥤ Dm} {resYht : Dt ⥤ Dn} {resYc : Dt ⥤ Dm}
    (aZh : QZh ⊣ resZh) (aZht : QZht ⊣ resZht) (aZc : QZc ⊣ resZc)
    (aYh : QYh ⊣ resYh) (aYht : QYht ⊣ resYht) (aYc : QYc ⊣ resYc)
    (αh : Fm ⋙ QYh ⟶ QZh ⋙ Fn) (αht : Fn ⋙ QYht ⟶ QZht ⋙ Ft) (αc : Fm ⋙ QYc ⟶ QZc ⋙ Ft)
    (δh : resZh ⋙ Fm ≅ Fn ⋙ resYh) (δht : resZht ⋙ Fn ≅ Ft ⋙ resYht)
    (δc : resZc ⋙ Fm ≅ Ft ⋙ resYc)
    (hh : mateEquiv aZh aYh (.mk _ _ _ _ αh) = δh.hom)
    (hht : mateEquiv aZht aYht (.mk _ _ _ _ αht) = δht.hom)
    (hc : mateEquiv aZc aYc (.mk _ _ _ _ αc) = δc.hom)
    (κZ : resZht ⋙ resZh ≅ resZc) (κY : resYht ⋙ resYh ≅ resYc)
    (dh : Fn ⋙ resYh ⟶ resZh ⋙ Fm) (dht : Ft ⋙ resYht ⟶ resZht ⋙ Fn)
    (dc : Ft ⋙ resYc ⟶ resZc ⋙ Fm) (ih : δh.inv = dh) (iht : δht.inv = dht) (ic : δc.inv = dc)
    (hyp' : ∀ W, dc.app W ≫ Fm.map (κZ.inv.app W) =
      κY.inv.app (Ft.obj W) ≫ resYh.map (dht.app W) ≫ dh.app (resZht.obj W))
    (K : Cm) :
    QYht.map (αh.app K) ≫ αht.app (QZh.obj K) ≫
        Ft.map ((Adjunction.leftAdjointCompIso aZh aZht aZc κZ).hom.app K) =
      (Adjunction.leftAdjointCompIso aYh aYht aYc κY).hom.app (Fm.obj K) ≫ αc.app K := by
  set rZ := Adjunction.leftAdjointCompIso aZh aZht aZc κZ
  set rY := Adjunction.leftAdjointCompIso aYh aYht aYc κY
  have hyp : ∀ W, Fm.map (κZ.inv.app W) ≫ δh.hom.app (resZht.obj W) ≫
      resYh.map (δht.hom.app W) ≫ κY.hom.app (Ft.obj W) = δc.hom.app W := fun W ↦ by
    subst ih iht ic
    rw [← cancel_epi (δc.inv.app W), reassoc_of% (hyp' W)]
    simp [← Functor.map_comp_assoc]
  -- unit relations of the reassociations
  have uZ : ∀ X, aZh.unit.app X ≫ resZh.map (aZht.unit.app (QZh.obj X)) ≫
      resZh.map (resZht.map (rZ.hom.app X)) = aZc.unit.app X ≫ κZ.inv.app (QZc.obj X) := by
    intro X
    have u := unit_conjugateEquiv (aZh.comp aZht) aZc rZ.inv X
    rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at u
    rw [Adjunction.comp_unit_app] at u
    rw [← cancel_mono (κZ.hom.app (QZc.obj X))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have n := κZ.hom.naturality (rZ.hom.app X)
    dsimp only [Functor.comp_map, Functor.comp_obj] at n u
    rw [n, ← Category.assoc, ← Category.assoc, u]
    simp [← Functor.map_comp]
  have uY : ∀ X, aYh.unit.app X ≫ resYh.map (aYht.unit.app (QYh.obj X)) ≫
      resYh.map (resYht.map (rY.hom.app X)) = aYc.unit.app X ≫ κY.inv.app (QYc.obj X) := by
    intro X
    have u := unit_conjugateEquiv (aYh.comp aYht) aYc rY.inv X
    rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at u
    rw [Adjunction.comp_unit_app] at u
    rw [← cancel_mono (κY.hom.app (QYc.obj X))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have n := κY.hom.naturality (rY.hom.app X)
    dsimp only [Functor.comp_map, Functor.comp_obj] at n u
    rw [n, ← Category.assoc, ← Category.assoc, u]
    simp [← Functor.map_comp]
  have mh := fun X ↦ unit_mateEquiv aZh aYh (.mk _ _ _ _ αh) X
  have mht := fun X ↦ unit_mateEquiv aZht aYht (.mk _ _ _ _ αht) X
  have mc := fun X ↦ unit_mateEquiv aZc aYc (.mk _ _ _ _ αc) X
  rw [hh] at mh
  rw [hht] at mht
  rw [hc] at mc
  dsimp only [TwoSquare.mk, Functor.comp_obj, Functor.id_obj] at mh mht mc
  apply ((aYh.comp aYht).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  -- right hand side
  rw [reassoc_of% (uY (Fm.obj K))]
  have nκ := κY.inv.naturality (αc.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nκ
  rw [← nκ, ← reassoc_of% (mc K)]
  -- left hand side
  have n1 := aYht.unit.naturality (αh.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at n1
  rw [← resYh.map_comp_assoc, ← n1, resYh.map_comp_assoc, ← reassoc_of% (mh K)]
  rw [← resYh.map_comp_assoc, ← mht (QZh.obj K), resYh.map_comp, Category.assoc]
  have n2 := δh.hom.naturality (aZht.unit.app (QZh.obj K))
  have n3 := δht.hom.naturality (rZ.hom.app K)
  have n4 := δh.hom.naturality (resZht.map (rZ.hom.app K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n2 n3 n4
  rw [← reassoc_of% n2, ← resYh.map_comp, ← n3, resYh.map_comp,
    ← reassoc_of% n4, ← Fm.map_comp_assoc, ← Fm.map_comp_assoc, Category.assoc, uZ,
    Fm.map_comp_assoc]
  congr 1
  rw [← hyp]
  simp

variable {Ym Yn Yt Zm Zn Zt : Type*} [Category Ym] [Category Yn] [Category Yt]
  [Category Zm] [Category Zn] [Category Zt]

private theorem whiskered_square_trans
    {resYh : Yn ⥤ Ym} {resYht : Yt ⥤ Yn} {resYc : Yt ⥤ Ym}
    {resZh : Zn ⥤ Zm} {resZht : Zt ⥤ Zn} {resZc : Zt ⥤ Zm}
    {Um um : Ym ⥤ Zm} {Un un : Yn ⥤ Zn} {Ut ut : Yt ⥤ Zt}
    (lm : Um ≅ um) (ln : Un ≅ un) (lt : Ut ≅ ut)
    (sh : resYh ⋙ um ≅ un ⋙ resZh) (sht : resYht ⋙ un ≅ ut ⋙ resZht)
    (sc : resYc ⋙ um ≅ ut ⋙ resZc)
    (κY : resYht ⋙ resYh ≅ resYc) (κZ : resZht ⋙ resZh ≅ resZc)
    (hyp : ∀ M, sc.hom.app M ≫ κZ.inv.app (ut.obj M) =
      um.map (κY.inv.app M) ≫ sh.hom.app (resYht.obj M) ≫ resZh.map (sht.hom.app M))
    (M : Yt) :
    (Functor.isoWhiskerLeft resYc lm ≪≫ sc ≪≫ Functor.isoWhiskerRight lt.symm resZc).hom.app M ≫
        κZ.inv.app (Ut.obj M) =
      Um.map (κY.inv.app M) ≫
        (Functor.isoWhiskerLeft resYh lm ≪≫ sh ≪≫
          Functor.isoWhiskerRight ln.symm resZh).hom.app (resYht.obj M) ≫
        resZh.map ((Functor.isoWhiskerLeft resYht ln ≪≫ sht ≪≫
          Functor.isoWhiskerRight lt.symm resZht).hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc, Functor.comp_obj, Functor.map_comp]
  have n1 := κZ.inv.naturality (lt.inv.app M)
  have n2 := lm.hom.naturality (κY.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1 n2
  rw [n1, reassoc_of% (hyp M), reassoc_of% n2]
  simp [← Functor.map_comp]

private theorem mate_trans_of_square
    {resYh : Yn ⥤ Ym} {resYht : Yt ⥤ Yn} {resYc : Yt ⥤ Ym}
    {resZh : Zn ⥤ Zm} {resZht : Zt ⥤ Zn} {resZc : Zt ⥤ Zm}
    {Um : Ym ⥤ Zm} {Un : Yn ⥤ Zn} {Ut : Yt ⥤ Zt} {Fm : Zm ⥤ Ym} {Fn : Zn ⥤ Yn} {Ft : Zt ⥤ Yt}
    (am : Um ⊣ Fm) (an : Un ⊣ Fn) (at' : Ut ⊣ Ft)
    (σh : resYh ⋙ Um ⟶ Un ⋙ resZh) (σht : resYht ⋙ Un ⟶ Ut ⋙ resZht)
    (σc : resYc ⋙ Um ⟶ Ut ⋙ resZc)
    (κY : resYht ⋙ resYh ≅ resYc) (κZ : resZht ⋙ resZh ≅ resZc)
    (hyp : ∀ M, σc.app M ≫ κZ.inv.app (Ut.obj M) =
      Um.map (κY.inv.app M) ≫ σh.app (resYht.obj M) ≫ resZh.map (σht.app M))
    (W : Zt) :
    (mateEquiv at' am (.mk _ _ _ _ σc)).app W ≫ Fm.map (κZ.inv.app W) =
      κY.inv.app (Ft.obj W) ≫ resYh.map ((mateEquiv at' an (.mk _ _ _ _ σht)).app W) ≫
        (mateEquiv an am (.mk _ _ _ _ σh)).app (resZht.obj W) := by
  apply (am.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  have cc := mateEquiv_counit at' am (.mk _ _ _ _ σc) W
  have ch := mateEquiv_counit an am (.mk _ _ _ _ σh) (resZht.obj W)
  have cht := mateEquiv_counit at' an (.mk _ _ _ _ σht) W
  dsimp only [Functor.comp_obj] at cc ch cht
  rw [am.counit_naturality, reassoc_of% cc, ch]
  dsimp only [TwoSquare.mk]
  have n1 := κZ.inv.naturality (at'.counit.app W)
  have n2 := σh.naturality ((mateEquiv at' an (.mk _ _ _ _ σht)).app W)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n1 n2
  rw [n1, reassoc_of% (hyp (Ft.obj W)), reassoc_of% n2, ← resZh.map_comp (Un.map _), cht]
  rw [resZh.map_comp]

private theorem upperStar_restriction_trans
    {resYh : Yn ⥤ Ym} {resYht : Yt ⥤ Yn} {resYc : Yt ⥤ Ym}
    {resZh : Zn ⥤ Zm} {resZht : Zt ⥤ Zn} {resZc : Zt ⥤ Zm}
    {Pm : Ym ⥤ Zm} {Pn : Yn ⥤ Zn} {Pt : Yt ⥤ Zt} {Sm : Zm ⥤ Ym} {Sn : Zn ⥤ Yn} {St : Zt ⥤ Yt}
    (am : Pm ⊣ Sm) (an : Pn ⊣ Sn) (at' : Pt ⊣ St)
    (cH : resZh ⋙ Sm ≅ Sn ⋙ resYh) (cHT : resZht ⋙ Sn ≅ St ⋙ resYht)
    (cC : resZc ⋙ Sm ≅ St ⋙ resYc)
    (uh : resYh ⋙ Pm ≅ Pn ⋙ resZh) (uht : resYht ⋙ Pn ≅ Pt ⋙ resZht)
    (uc : resYc ⋙ Pm ≅ Pt ⋙ resZc)
    (th' : ∀ X, am.unit.app (resYh.obj X) ≫ Sm.map (uh.hom.app X) =
      resYh.map (an.unit.app X) ≫ cH.inv.app (Pn.obj X))
    (tht' : ∀ X, an.unit.app (resYht.obj X) ≫ Sn.map (uht.hom.app X) =
      resYht.map (at'.unit.app X) ≫ cHT.inv.app (Pt.obj X))
    (tc : ∀ X, am.unit.app (resYc.obj X) ≫ Sm.map (uc.hom.app X) =
      resYc.map (at'.unit.app X) ≫ cC.inv.app (Pt.obj X))
    (ρY : resYht ⋙ resYh ≅ resYc) (ρZ : resZht ⋙ resZh ≅ resZc)
    (hρ : ∀ M, cC.inv.app M ≫ Sm.map (ρZ.inv.app M) = ρY.inv.app (St.obj M) ≫
      resYh.map (cHT.inv.app M) ≫ cH.inv.app (resZht.obj M)) (X : Yt) :
    uc.hom.app X ≫ ρZ.inv.app (Pt.obj X) =
      Pm.map (ρY.inv.app X) ≫ uh.hom.app (resYht.obj X) ≫ resZh.map (uht.hom.app X) := by
  apply (am.homEquiv _ _).injective
  rw [am.homEquiv_unit, am.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [reassoc_of% (tc X), hρ]
  have n1 := ρY.inv.naturality (at'.unit.app X)
  have n2 := am.unit.naturality (ρY.inv.app X)
  have n3 := cH.inv.naturality (uht.hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at n1 n2 n3
  rw [reassoc_of% n1, ← reassoc_of% n2, reassoc_of% (th' (resYht.obj X)), ← n3,
    ← resYh.map_comp_assoc, ← tht']
  simp


end MatePasting

section ScalarMateCoherence

/-- Direct image commutes with the identity restriction comparisons. -/
theorem lowerStar_restrictionSelf {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (Ring l E n))) :
    ((p)_*[ModuleCat.{u + 1} (Ring l E n)]).map ((restrictionSelf l E Z n).hom.app M) =
      (restrictionSelf l E Y n).hom.app (((p)_*[ModuleCat.{u + 1} (Ring l E n)]).obj M) := by
  ext U x
  rfl

/-- The inverse image comparison with restriction of scalars along the identity quotient is
compatible with the identity restriction comparisons. -/
theorem upperStarRestrictScalarsIsoSheaf_restrictionSelf {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (n : ℕ) (X : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Ring l E n))) :
    (upperStarRestrictScalarsIsoSheaf (quotient l E (le_refl n)) p).hom.app X ≫
        (restrictionSelf l E Z n).hom.app (((p)^*[ModuleCat.{u + 1} (Ring l E n)]).obj X) =
      ((p)^*[ModuleCat.{u + 1} (Ring l E n)]).map ((restrictionSelf l E Y n).hom.app X) := by
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (Ring l E n)) p
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, Functor.map_comp,
    reassoc_of% (upperStarRestrictScalarsIsoSheaf_hom_app_transpose _ p X),
    lowerStar_restrictionSelf]
  have := (restrictionSelf l E Y n).hom.naturality (adj.unit.app X)
  refine this.trans ?_
  simp

private theorem unit_selfReduction (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategoryModule (Ring l E n) T) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E (le_refl n))) :
        Q l E T (le_refl n) ⊣ _).unit.app K ≫
      (Functor.mapDerivedCategoryNatIso (restrictionSelf l E T n) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app ((Q l E T (le_refl n)).obj K) =
      (selfReduction l E T n).inv.app K := by
  exact (unit_conjugateEquiv_symm (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E (le_refl n)))) Adjunction.id
    (Functor.mapDerivedCategoryNatIso (restrictionSelf l E T n) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom K).trans (Category.id_comp _)

/-- The quotient map along a composite is the composite of the quotient maps. -/
theorem quotient_trans {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n) :
    quotient l E (ht.trans h) = (quotient l E ht).comp (quotient l E h) :=
  RingHom.ext fun x ↦ Quotient.inductionOn x fun _ ↦ rfl

/-- Restriction of scalars along successive quotients, on sheaves. -/
abbrev restrictionComp (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n) :=
  Sheaf.restrictScalarsCompIso T.smallEtaleTopology (quotient l E h) (quotient l E ht)
    (quotient l E (ht.trans h)) (quotient_trans l E h ht)

/-- Direct image commutes with the composition comparisons of restriction of scalars. -/
theorem lowerStar_restrictionComp {Z Y : Scheme.{u}} (p : Z ⟶ Y) {m n t : ℕ} (h : n ≤ m)
    (ht : t ≤ n) (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (Ring l E t))) :
    ((p)_*[ModuleCat.{u + 1} (Ring l E m)]).map ((restrictionComp l E Z h ht).inv.app M) =
      (restrictionComp l E Y h ht).inv.app (((p)_*[ModuleCat.{u + 1} (Ring l E t)]).obj M) := by
  ext U x
  rfl

/-- Restriction of scalars commutes with direct image, as the identity. -/
private def lowerStarRestriction {Z Y : Scheme.{u}} (p : Z ⟶ Y) {m n : ℕ}
    (h : n ≤ m) :
    Sheaf.restrictScalars Z.smallEtaleTopology (quotient l E h) ⋙
        (p)_*[ModuleCat.{u + 1} (Ring l E m)] ≅
      (p)_*[ModuleCat.{u + 1} (Ring l E n)] ⋙
        Sheaf.restrictScalars Y.smallEtaleTopology (quotient l E h) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext U x; rfl)

private theorem lowerStarRestriction_inv_app {Z Y : Scheme.{u}} (p : Z ⟶ Y) {m n : ℕ} (h : n ≤ m)
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (Ring l E n))) :
    (lowerStarRestriction l E p h).inv.app M = 𝟙 _ := rfl

/-- The inverse image comparisons with restriction of scalars along successive quotients compose
to the comparison along the composite quotient. -/
theorem upperStarRestrictScalarsIsoSheaf_restrictionComp {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    {m n t : ℕ} (h : n ≤ m) (ht : t ≤ n)
    (X : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Ring l E t))) :
    (upperStarRestrictScalarsIsoSheaf (quotient l E (ht.trans h)) p).hom.app X ≫
        (restrictionComp l E Z h ht).inv.app (((p)^*[ModuleCat.{u + 1} (Ring l E t)]).obj X) =
      ((p)^*[ModuleCat.{u + 1} (Ring l E m)]).map ((restrictionComp l E Y h ht).inv.app X) ≫
        (upperStarRestrictScalarsIsoSheaf (quotient l E h) p).hom.app
          ((Sheaf.restrictScalars Y.smallEtaleTopology (quotient l E ht)).obj X) ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology (quotient l E h)).map
          ((upperStarRestrictScalarsIsoSheaf (quotient l E ht) p).hom.app X) := by
  refine upperStar_restriction_trans (upperStarLowerStarAdjunction _ p)
    (upperStarLowerStarAdjunction _ p) (upperStarLowerStarAdjunction _ p)
    (lowerStarRestriction l E p h) (lowerStarRestriction l E p ht)
    (lowerStarRestriction l E p (ht.trans h)) _ _ _ (fun X ↦ ?_) (fun X ↦ ?_) (fun X ↦ ?_)
    _ _ (fun M ↦ ?_) X
  · exact (upperStarRestrictScalarsIsoSheaf_hom_app_transpose _ p X).trans (Category.comp_id _).symm
  · exact (upperStarRestrictScalarsIsoSheaf_hom_app_transpose _ p X).trans (Category.comp_id _).symm
  · exact (upperStarRestrictScalarsIsoSheaf_hom_app_transpose _ p X).trans (Category.comp_id _).symm
  · exact ((Category.id_comp _).trans (lowerStar_restrictionComp l E p h ht M)).trans
      (by
        rw [lowerStarRestriction_inv_app, lowerStarRestriction_inv_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])

/-- The scalar mates along successive quotients compose to the scalar mate along the composite
quotient, through the tensor reassociations `reassoc`. -/
theorem scalarMate_quotient_trans {Z Y : Scheme.{u}} (p : Z ⟶ Y) {m n t : ℕ} (h : n ≤ m)
    (ht : t ≤ n) (K : DerivedCategoryModule (Ring l E m) Z) :
    (Q l E Y ht).map ((scalarMate (quotient l E h) p).app K) ≫
        (scalarMate (quotient l E ht) p).app ((Q l E Z h).obj K) ≫
        (F l E p t).map ((reassoc l E Z h ht).hom.app K) =
      (reassoc l E Y h ht).hom.app ((F l E p m).obj K) ≫
        (scalarMate (quotient l E (ht.trans h)) p).app K := by
  obtain ⟨δh, hδh, mh⟩ := scalarMate_restrictionTranspose (quotient l E h) p
  obtain ⟨δht, hδht, mht⟩ := scalarMate_restrictionTranspose (quotient l E ht) p
  obtain ⟨δc, hδc, mc⟩ := scalarMate_restrictionTranspose (quotient l E (ht.trans h)) p
  refine mate_trans_of_transpose
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology
      (quotient l E h)) : Q l E Z h ⊣ _)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology
      (quotient l E ht)) : Q l E Z ht ⊣ _)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology
      (quotient l E (ht.trans h))) : Q l E Z (ht.trans h) ⊣ _)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology
      (quotient l E h)) : Q l E Y h ⊣ _)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology
      (quotient l E ht)) : Q l E Y ht ⊣ _)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology
      (quotient l E (ht.trans h))) : Q l E Y (ht.trans h) ⊣ _)
    _ _ _ δh δht δc mh mht mc
    (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology (quotient_trans l E h ht))
    (Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology (quotient_trans l E h ht))
    _ _ _ hδh hδht hδc
    (fun W ↦ ?_) K
  have hE := upperStarRestrictScalarsIsoSheaf_restrictionComp l E p h ht
  have hD := Functor.mapDerivedCategorySquareIso_compIso
    (upperStarRestrictScalarsIsoSheaf (quotient l E h) p)
    (upperStarRestrictScalarsIsoSheaf (quotient l E ht) p)
    (upperStarRestrictScalarsIsoSheaf (quotient l E (ht.trans h)) p)
    (restrictionComp l E Y h ht) (restrictionComp l E Z h ht) hE
  have hC := whiskered_square_trans (leftDerivedUpperStarIsoMapDerivedCategory _ p)
    (leftDerivedUpperStarIsoMapDerivedCategory _ p)
    (leftDerivedUpperStarIsoMapDerivedCategory _ p) _ _ _ _ _ hD
  exact mate_trans_of_square (derivedUpperStarLowerStarAdjunction _ p)
    (derivedUpperStarLowerStarAdjunction _ p) (derivedUpperStarLowerStarAdjunction _ p)
    (scalarRestrictionPullbackIso (quotient l E h) p).hom
    (scalarRestrictionPullbackIso (quotient l E ht) p).hom
    (scalarRestrictionPullbackIso (quotient l E (ht.trans h)) p).hom _ _ hC W

/-- The scalar mate along the identity quotient is the identity, through the identity
comparisons `selfReduction`. -/
theorem scalarMate_quotient_refl {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (K : DerivedCategoryModule (Ring l E n) Z) :
    (scalarMate (quotient l E (le_refl n)) p).app K ≫
        (F l E p n).map ((selfReduction l E Z n).hom.app K) =
      (selfReduction l E Y n).hom.app ((F l E p n).obj K) := by
  obtain ⟨δ, hδinv, hδ⟩ := scalarMate_restrictionTranspose (quotient l E (le_refl n)) p
  refine mate_refl_of_transpose (F l E p n)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology
      (quotient l E (le_refl n))) : Q l E Z (le_refl n) ⊣ _)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology
      (quotient l E (le_refl n))) : Q l E Y (le_refl n) ⊣ _)
    (scalarMate (quotient l E (le_refl n)) p) δ hδ
    (selfReduction l E Z n) (selfReduction l E Y n)
    (Functor.mapDerivedCategoryNatIso (restrictionSelf l E Z n) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (restrictionSelf l E Y n) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (unit_selfReduction l E Z n) (unit_selfReduction l E Y n) ?_ K
  intro K
  rw [hδinv]
  refine mate_refl_of_square (derivedUpperStarLowerStarAdjunction _ p)
    (scalarRestrictionPullbackIso (quotient l E (le_refl n)) p).hom _ _ ?_ K
  intro M
  exact whiskered_square_unitors (leftDerivedUpperStarIsoMapDerivedCategory _ p) _ _ _
    (Functor.mapDerivedCategorySquareIso_unitors _ _ _
      (upperStarRestrictScalarsIsoSheaf_restrictionSelf l E p n)) M

end ScalarMateCoherence


variable {Z Y : Scheme.{u}} (p : Z ⟶ Y)
  (G : ∀ n : ℕ, DerivedCategoryModule (Ring l E n) Y ⥤
    DerivedCategoryModule (Ring l E n) Z)
  (adj : ∀ n : ℕ, F l E p n ⊣ G n)

/-- The right-adjoint mate of the inverse of the canonical proper comparison. -/
def b {m n : ℕ} (h : n ≤ m)
    (q : F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n) :
    G m ⋙ Q l E Z h ⟶ Q l E Y h ⋙ G n :=
  (mateEquiv (adj m) (adj n) (.mk _ _ _ _ q.inv))

/-- For a proper morphism `p` of finite type schemes over a field of characteristic
`p₀ ≠ ℓ`, the quotient mate of the exceptional inverse images, built from the scalar mate, is
an isomorphism on ctf objects. -/
theorem isIso_b_app_of_ctf {m n : ℕ} (h : n ≤ m)
    (q : F l E p m ⋙ Q l E Y h ≅ Q l E Z h ⋙ F l E p n)
    (hq : q.hom = scalarMate (quotient l E h) p)
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀] (hl : l ≠ p₀)
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
  refine ⟨fun n L hL ↦ ctf_obj_of_adjunction l E p n (G n) (adj n) p₀ k _hl L hL, @q,
    fun h ↦ rfl, fun h L hL ↦ isIso_b_app_of_ctf l E p G adj h (q h) rfl p₀ k _hl L hL,
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
