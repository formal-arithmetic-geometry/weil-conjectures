module
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import all Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Direct images preserve bounded constructibility

Source: Weil blueprint, `def-weil-ordinary-compact-cohomology` (blueprint:
lem-weil-structure-direct-images-constructible).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The coefficient prime is a unit in the finite-field fibre.
Source: blueprint `def-weil-ordinary-compact-cohomology`, finite-field hypotheses
(blueprint: lem-weil-structure-direct-images-constructible).
Proof: the cardinality of the base field gives characteristic D.p, and its algebraic
closure has the same characteristic. If the image of l vanished, D.p would divide l.
Since both are prime, this would force l = D.p, contrary to hl. Thus l is nonzero
in the field D.k, and hence is a unit. -/
theorem finiteFieldDatumPrimeUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  have _ : Fact D.p.Prime := ⟨D.prime⟩
  have _ : CharP D.k₀ D.p :=
    charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  have _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hne : (l : D.k) ≠ 0 := by
    intro h
    have hdvd : D.p ∣ l := by
      exact (CharP.cast_eq_zero_iff D.k D.p l).mp h
    obtain h | h := (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd
    · exact D.prime.ne_one h
    · exact hl h.symm
  exact isUnit_iff_ne_zero.mpr hne

/-- For the finite-field datum and separated finite-type structure morphism, ordinary and
compact-support direct images of bounded constructible objects remain in the corresponding
bounded constructible categories at all four coefficient levels.  The statement records the
finite level with the intrinsic constructibility predicate, the integral level with the
specified derived-limit direct image and compact-support value, and the rational and
common-stage levels by the scalar-localization and finite-stage constructions.
Source: blueprint node `def-weil-ordinary-compact-cohomology`, order 1510
(blueprint: lem-weil-structure-direct-images-constructible).
Proof:
1. The finite-field cardinality determines the characteristic. Since l and p are
prime and distinct, l is nonzero in D.k and hence a unit.
2. At finite level restrict modules to fixed coefficients, and use the fixed
etale-origin construction. The DVR maximal-ideal description shows that l^n
annihilates the coefficient ring, so finite-type etale direct-image finiteness
applies. The bounded-below comparison and restriction direct-image isomorphisms
transfer constructibility and a bounded cohomological interval to the required
pro-etale direct image.
3. Apply finiteCompactSupportConstructibility to the same finite input.
4. Apply sfIntegralDirectImage_constructible to L. The constructed integral
compact-support value already stores its constructibility proof.
5. Localize the two integral constructible objects. The underlying-object
identifications are reflexive. Pair each rational object with E₀ to obtain the
common-stage objects; their underlying derived objects are again identified by
reflexivity. -/
theorem directImages_constructible
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω)
    (n : ℕ) (hn : 1 ≤ n)
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    {Kₙ : proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)}
    (hKₙ : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
      n hn Y Kₙ)
    {K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y}
    (L : @SfIntegralDirectImage l inferInstance (Coefficient.{u} l Ω E₀)
      inferInstance inferInstance inferInstance
      Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
        let : HasCountableProducts
            (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
              (Spec (CommRingCat.of D.k)))) :=
          integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
            (Spec (CommRingCat.of D.k))
        infer_instance))
    : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)).obj Kₙ) ∧
      intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((@AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
            (Y ↘ Spec (CommRingCat.of D.k)) c
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n) _
            (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn)).obj Kₙ) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k (by
          exact finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
          (finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj.obj
          (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj.obj
          ((sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
            (finiteFieldDatumPrimeUnit D l hl) c K).obj) := by
  classical
  let E := Coefficient.{u} l Ω E₀
  let s := Spec (CommRingCat.of D.k)
  let : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E s)) :=
    integralOperationsDerivedCountableProducts l E s
  have hL : sfIntegralConstructible l E s L.obj :=
    ((sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
      E (Y ↘ s) K.obj K.property).2.1 L).1
  let I : sfIntegralConstructibleCategory l E s := ⟨L.obj, hL⟩
  let C := sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K
  let R := (sfRationalConstructibleLocalization l E s).obj I
  let S := (sfRationalConstructibleLocalization l E s).obj C
  refine ⟨?_, ?_, hL, C.property, R, rfl, S, rfl,
    ⟨E₀, R⟩, rfl, ?_, ⟨E₀, S⟩, rfl, ?_⟩
  · let B := Padic.coefficientExtensionRing l E n
    let : Finite B := Padic.finite_coefficientExtensionRing l E n hn
    let A := ULift.{u + 1, u} B
    let RX := proEtaleModuleRestriction Y B
    let RY := proEtaleModuleRestriction s B
    have : RX.Additive := { map_add := by intros; rfl }
    have : RY.Additive := { map_add := by intros; rfl }
    have : RX.IsEquivalence := proEtaleModuleRestriction_isEquivalence Y B
    have : RY.IsEquivalence := proEtaleModuleRestriction_isEquivalence s B
    let M := RX.mapDerivedCategory.obj Kₙ
    have hc (q : ℤ) : ProEtale.IsConstructible A
        ((DerivedCategory.homologyFunctor _ q).obj M) := by
      exact ProEtale.isConstructible_of_iso
        ((RX.mapDerivedCategoryHomologyFunctorIso q).app Kₙ)
        ((proEtaleModuleRestriction_constructible_iff Y B _).mp (hKₙ.2 q))
    obtain ⟨a, ha⟩ := hKₙ.1.bddBelow
    obtain ⟨b, hb⟩ := hKₙ.1.bddAbove
    have hv (q : ℤ) (hq : q < a ∨ b < q) :
        IsZero ((DerivedCategory.homologyFunctor _ q).obj Kₙ) := by
      by_contra h
      rcases hq with hq | hq
      · exact (not_le_of_gt hq) (ha h)
      · exact (not_le_of_gt hq) (hb h)
    obtain ⟨J, hJ, ⟨eJ⟩⟩ := ProEtale.fixedDerivedOrigin Y A M hc a b
      (fun q hq ↦ RX.isZero_homologyFunctor_mapDerivedCategory_obj (hv q hq))
    have er := (ProEtale.restrictionDerivedDirectImageIso (Y ↘ s) B).app Kₙ
    change RY.mapDerivedCategory.obj
        ((proEtaleConstantDerivedDirectImage (Y ↘ s) B).obj Kₙ) ≅
      (ProEtale.lowerStar (ModuleCat A) (Y ↘ s)).rightDerivedFunctor.obj M at er
    have hzero : ((l ^ n : ℕ) : B) = 0 := by
      let h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
      have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
        change spectralNorm (Padic l) E (l : E) < 1
        rw [show (l : E) = algebraMap (Padic l) E (l : Padic l) by simp]
        rw [spectralNorm_extends]
        exact Padic.norm_p_lt_one
      have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
          Padic.coefficientExtensionMaximalIdeal l E :=
        (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
      have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) =
          Padic.coefficientExtensionMaximalIdeal l E :=
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
      have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
          Padic.coefficientExtensionIdeal l E n := by
        change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ n
        rw [hgen]
        exact Ideal.pow_mem_pow hlm n
      change ((l ^ n : ℕ) : Padic.coefficientExtensionIntegers l E ⧸
        Padic.coefficientExtensionIdeal l E n) = 0
      rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
        Ideal.Quotient.eq_zero_iff_mem]
      simpa only [Nat.cast_pow] using hpow
    have hA : Etale.IsSmoothBaseChangeCoefficients (l ^ n) A s := by
      refine ⟨pow_pos (Fact.out : l.Prime).pos _, inferInstance, ?_, ?_⟩
      · apply ULift.down_injective
        exact hzero
      · simpa only [map_pow, map_natCast, ← Nat.cast_pow] using
          ((finiteFieldDatumPrimeUnit D l hl).pow n).map (Scheme.ΓSpecIso (.of D.k)).inv.hom
    let f := Y ↘ s
    let νX := ProEtale.comparisonUpperStar (ModuleCat A) Y
    let νY := ProEtale.comparisonUpperStar (ModuleCat A) s
    let F := Etale.lowerStar (ModuleCat A) f
    let G := ProEtale.lowerStar (ModuleCat A) f
    have hFJ := Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
      D.k A (l ^ n) hA f (𝟙 s) f (by simp) J hJ
    obtain ⟨aJ, bJ, _, hvJ⟩ := hJ.2
    let Jp : DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat A)) :=
      ⟨J, ⟨aJ, (DerivedCategory.isGE_iff J aJ).2
        (fun q hq ↦ hvJ q (Or.inl hq))⟩⟩
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
        (ProEtale.lowerStarComparisonUpperStarBaseChange f (ModuleCat A))) :=
      ProEtale.isIso_comparisonDirectImagePlus A f
    let e := asIso (Functor.rightDerivedFunctorPlusBaseChange
      (ProEtale.lowerStarComparisonUpperStarBaseChange f (ModuleCat A)))
    let eOut : νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj J) ≅
        RY.mapDerivedCategory.obj ((proEtaleConstantDerivedDirectImage f B).obj Kₙ) :=
      νY.mapDerivedCategory.mapIso (F.rightDerivedFunctorPlusCompatibility.app Jp).symm ≪≫
        (νY.mapDerivedCategoryPlusCompatibility.app (F.rightDerivedFunctorPlus.obj Jp)).symm ≪≫
        DerivedCategory.Plus.ι.mapIso (e.app Jp) ≪≫
        G.rightDerivedFunctorPlusCompatibility.app (νX.mapDerivedCategoryPlus.obj Jp) ≪≫
        G.rightDerivedFunctor.mapIso (νX.mapDerivedCategoryPlusCompatibility.app Jp) ≪≫
        G.rightDerivedFunctor.mapIso eJ ≪≫ er.symm
    obtain ⟨aO, bO, _, hvO⟩ := hFJ.2
    have hz (q : ℤ) (hq : q < aO ∨ bO < q) :
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((proEtaleConstantDerivedDirectImage f B).obj Kₙ)) := by
      apply RY.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      exact (νY.map_isZero (hvO q hq)).of_iso
        ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
          (DerivedCategory.homologyFunctor _ q).mapIso eOut).symm
    constructor
    · apply (Set.finite_Icc aO bO).subset
      intro q hq
      by_contra h
      exact hq (hz q (by simpa only [Set.mem_Icc, not_and_or, not_le] using h))
    · intro q
      apply (proEtaleModuleRestriction_constructible_iff s B _).mpr
      have hq : Scheme.IsConstructibleSheaf
          ((DerivedCategory.homologyFunctor _ q).obj (F.rightDerivedFunctor.obj J)) :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)
      exact ProEtale.isConstructible_of_iso
        ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
          (DerivedCategory.homologyFunctor _ q).mapIso eOut ≪≫
          (RY.mapDerivedCategoryHomologyFunctorIso q).symm.app _)
        (ProEtale.isConstructible_comparisonUpperStar_obj _)
  · exact ((finiteCompactSupportConstructibility l E D.k
      (finiteFieldDatumPrimeUnit D l hl) n hn (Y ↘ s)).1 c).2 Kₙ hKₙ
  · exact HEq.rfl
  · exact HEq.rfl

end WeilConjectures
