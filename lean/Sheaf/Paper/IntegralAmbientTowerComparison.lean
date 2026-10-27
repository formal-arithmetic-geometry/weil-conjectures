/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.IntegralAmbientDirectImageEncoding
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.Paper.IntegralCoefficientModelRealization
import Sheaf.Paper.CompletedConstantPresentationTransport
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow

/-! # Ordinary integral direct image and its finite reduction tower

Source: Bhatt--Scholze, Lemmas 6.5.9(2),(3) and 5.4.3
(blueprint: lem-sfb-integral-ambient-tower-comparison).

The coefficient comparisons preserve the specified quotient maps. All derived
categories are ordinary ambient categories. The strict tower map and its augmentation
are the normalized adic projection mate, before any derived inverse limit is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme.IntegralAmbientTower
attribute [-instance] ConstantScalarRestriction.fixedAbelian
attribute [-instance] ConstantScalarRestriction.fixedPreadditive
attribute [-instance] ConstantScalarRestriction.fixedZeroMorphisms


variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- Finiteness, l-power annihilation and the normalized finite free resolution.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: l=πa implies l^(n+1)=π^(n+1)a^(n+1); it annihilates the quotient.
The cone of multiplication by π^(n+1) has only the two displayed free terms.
Its degree -1 cohomology is zero since the valuation ring is a domain, and its
zeroth cohomology is precisely the quotient. Augment by the quotient map, giving
the normalization on the degree-zero inclusion. This is the resolution used in
the perfect projection formula of lemma-weil-pbc-perfect-projection-formula. -/
theorem finiteResolution (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (n : ℕ) :
    (∀ x : integers.{u} l E ⧸ (Ideal.span {ULift.up π}) ^ (n + 1), l ^ (n + 1) • x = 0) ∧
      ∃ ε : resolution.{u} l E π n ⟶ quotientComplex.{u} l E π n,
        QuasiIso ε ∧
        (resolution.{u} l E π n).IsStrictlyGE (-1) ∧
        (resolution.{u} l E π n).IsStrictlyLE 0 ∧
        HasFiniteFreeTerms (resolution.{u} l E π n) := by
  let R := integers.{u} l E
  let M := ModuleCat.of R R
  let a : R := ULift.up π ^ (n + 1)
  let I : Ideal R := (Ideal.span {ULift.up π}) ^ (n + 1)
  have hI : I = Ideal.span {a} := Ideal.span_singleton_pow _ _
  let e : R ≃+* PadicAlgCl.integers l E.1 := ULift.ringEquiv
  have : IsDomain R := e.toMulEquiv.isDomain _
  have hπ0 : π ≠ 0 := by
    intro h
    apply PadicAlgCl.maximalIdeal_integers_ne_bot l E.1
    rw [← hπ, h, Ideal.span_singleton_eq_bot.mpr rfl]
  have ha : a ≠ 0 := pow_ne_zero _ (fun h ↦ hπ0 (congrArg ULift.down h))
  let m : M ⟶ M := ModuleCat.ofHom ((LinearMap.lsmul R R) a)
  let q : M ⟶ ModuleCat.of R (R ⧸ I) := ModuleCat.ofHom I.mkQ
  have hmq : m ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk I (a * x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hI, Ideal.mem_span_singleton]
    exact dvd_mul_right a x
  let S := ShortComplex.mk m q hmq
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      have hx' : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [hI, Ideal.mem_span_singleton] at hx'
      obtain ⟨y, hy⟩ := hx'
      exact ⟨y, hy.symm⟩
    · change Mono m
      rw [ModuleCat.mono_iff_injective]
      intro x y h
      exact mul_left_cancel₀ ha h
    · change Epi q
      rw [ModuleCat.epi_iff_surjective]
      exact I.mkQ_surjective
  let F := CochainComplex.singleFunctor (ModuleCat.{u + 1} R) 0
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (HomologicalComplex.single (ModuleCat.{u + 1} R) (.up ℤ) 0)
    infer_instance
  have : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (HomologicalComplex.single (ModuleCat.{u + 1} R) (.up ℤ) 0)
    infer_instance
  have hs := hS.map_of_exact F
  refine ⟨(integral_coefficient_model_realization l E π hπ).2.2.2.2.2.1 n,
    CochainComplex.mappingCone.descShortComplex (S.map F),
    CochainComplex.mappingCone.quasiIso_descShortComplex hs, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [resolution, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [resolution, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  · have hterm (i : ℤ) : Module.Free R ((F.obj M).X i) ∧
        Module.Finite R ((F.obj M).X i) := by
      by_cases hi : i = 0
      · subst i
        change Module.Free R R ∧ Module.Finite R R
        exact ⟨Module.Free.self R, Module.Finite.self R⟩
      · have hz : IsZero ((F.obj M).X i) :=
          HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
        have := ModuleCat.subsingleton_of_isZero hz
        exact ⟨inferInstance, inferInstance⟩
    intro i
    have := (hterm (i + 1)).1
    have := (hterm (i + 1)).2
    have := (hterm i).1
    have := (hterm i).2
    let t := HomologicalComplex.homotopyCofiber.XIsoBiprod (multiplication l E π n)
      i (i + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _
    exact ⟨Module.Free.of_equiv t.symm.toLinearEquiv,
      Module.Finite.equiv t.symm.toLinearEquiv⟩

/-- The canonical coefficient models exist, without hypotheses on the scheme.
Source: Bhatt--Scholze, Section 6.5; Stacks 09BT
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: use sk-prop-sfb-qlbar-colimit-x on the actual profinite quotient tower.
Finite continuous coefficients identify with constants by their local constant
sections. Transport ULift through the quotient by the class-of-a map; it preserves
all transition maps. The inverse-limit universal property gives the completed
comparison and its projection equation. Reconstructing section rings preserves
these identities and the pointwise scalar formula. Uniqueness follows locally
from constant sections, and then from the jointly monic limit projections. -/
theorem coefficientModel_exists (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (T : Scheme.{u}) : Nonempty (CoefficientModel l E π hπ T) := by
  exact ((integral_coefficient_model_realization l E π hπ).2.2.2.2.2.2.1 T).1

/-- The canonical encodings exist for every morphism and every positive finite level.
Source: Bhatt--Scholze, Section 6.5; Stacks 0D6E
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: the sectionModuleEquivalence is identity on the underlying abelian sheaf,
and scalar transport uses the projection-normalized ring comparisons. The
coefficient inverse-image identity of lem-weil-pbc-profinite-coefficient-inverse-image
therefore makes the ordinary direct-image actions equal. The identity section maps
give the ordinary comparisons. Exact equivalences preserve K-injectives; uniqueness
of total right-derived functors gives the derived comparisons with the displayed
unit normalization. Apply the same argument to each constant finite quotient,
using its constants-to-functions map. No scheme hypothesis is used here. -/
theorem encodings (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (CX : CoefficientModel l E π hπ X) (CY : CoefficientModel l E π hπ Y) :
    Nonempty (AmbientEncoding l E f CX CY) ∧
      ∀ n : ℕ, Nonempty (FinitePushEncoding l E (π := π) (hπ := hπ) f n) := by
  have h := (integral_coefficient_model_realization l E π hπ).2.2.2.2.2.2.2 f CX CY
  exact h.2.2

private theorem roos_object_iso
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : ℕ → C} [HasProduct B] (f : ∀ n, B (n + 1) ⟶ B n)
    {K L : C} {p : K ⟶ ∏ᶜ B} {q : L ⟶ ∏ᶜ B}
    {δ : ∏ᶜ B ⟶ K⟦(1 : ℤ)⟧} {ε : ∏ᶜ B ⟶ L⟦(1 : ℤ)⟧}
    (hK : IsDerivedLimitTriangle f K p δ) (hL : IsDerivedLimitTriangle f L q ε) :
    Nonempty (K ≅ L) := by
  let tK := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ
  let tL := Pretriangulated.Triangle.mk q (towerTransitionEndomorphism f) ε
  let e := Pretriangulated.isoTriangleOfIso₁₂ tK.rotate tL.rotate
    (Pretriangulated.rot_of_distTriang _ hK) (Pretriangulated.rot_of_distTriang _ hL)
    (Iso.refl _) (Iso.refl _) (by
      change towerTransitionEndomorphism f ≫ 𝟙 _ = 𝟙 _ ≫ towerTransitionEndomorphism f
      simp only [Category.comp_id, Category.id_comp])
  exact ⟨(shiftFunctor C (1 : ℤ)).preimageIso
    (Pretriangulated.Triangle.π₃.mapIso e)⟩

private theorem quotient_products (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    HasCountableProducts (d.derived T) := by
  let R := d.completedRing T
  let B := reductionModules T R
  have : HasFiniteBiproducts B := CategoryTheory.Abelian.hasFiniteBiproducts
  have : CountableAB4Star B := by
    have : (lim (J := Discrete ℕ) (C := B)).PreservesEpimorphisms :=
      { preserves := by
          intro F G f hf
          have h := (ProEt.countableProducts_exact.{u, u, 0} T R).2.2
            ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
            (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map f = (Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    have := hasExactLimitsOfShape_of_preservesEpi B (Discrete ℕ)
    exact CountableAB4Star.of_hasExactLimitsOfShape_nat B
  exact (derivedCategory_countableProducts_core.{0} B).choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_of_iso_completion (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : d.derived T)
    (e : K ≅ (completedRlim T (d.completedRing T)).obj
      ((completedReductionTower T d).obj K)) : d.TowerComplete T K := by
  obtain ⟨D⟩ := completed_constant_presentation_transport T d
  let F := D.equivalence.functor
  let J := completedCechTopology T
  let G := ConstantCompletion.completion J A d.ideal true
  let η := ConstantCompletion.completionUnit J A d.ideal true
  have : IsNoetherianRing A := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  obtain ⟨_, _, hc, _, hi⟩ :=
    ConstantCompletion.koszul_quotient_reflector J A d.ideal true r a ha
  obtain ⟨q, hq⟩ := D.quotient K
  let e' : F.obj K ≅ G.obj (F.obj K) := F.mapIso e ≪≫ q
  have : IsIso (η.app (G.obj (F.obj K))) := (hi _).mpr (hc _)
  have hn := η.naturality e'.hom
  dsimp only [Functor.id_map] at hn
  have : IsIso (η.app (F.obj K) ≫ G.map e'.hom) := by
    rw [← hn]
    infer_instance
  have : IsIso (η.app (F.obj K)) := IsIso.of_isIso_comp_right _ (G.map e'.hom)
  have : IsIso (F.map ((completedQuotientCompletionUnit T d).app K) ≫ q.hom) := by
    rw [hq]
    exact ‹IsIso (η.app (F.obj K))›
  have : IsIso (F.map ((completedQuotientCompletionUnit T d).app K)) :=
    IsIso.of_isIso_comp_right _ q.hom
  have h := isIso_of_reflects_iso ((completedQuotientCompletionUnit T d).app K) F
  unfold AdicCoefficientDatum.TowerComplete AdicCoefficientDatum.completionUnit
  simpa only [completedQuotientCompletionUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, AdicCoefficientDatum.constantRlimAdjunction,
    completedReductionAugmentation] using h

/-- Roos completeness and invertibility of the specified strict quotient completion
unit coincide; the actual quotient-unit legs are retained throughout.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks 08TC and 099N
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: a Roos triangle gives an isomorphism with the derived quotient limit.
That limit is intrinsically complete by the Koszul completion reflector; hence
so is the input. Koszul reconstruction then identifies its actual intrinsic unit
with the specified quotient unit and makes it invertible. Conversely transport
the canonical strict-limit Roos triangle along that unit. This is precisely the
argument in lem-pur-completed-coefficient-pushforward-comparison, Steps 6--7;
it does not select an arbitrary lifting of the Roos product arrow. -/
theorem complete_iff (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (T : Scheme.{u}) (K : (datum.{u} l E π hπ).derived T) :
    (datum.{u} l E π hπ).quotientRoosComplete T K ↔
      (datum.{u} l E π hπ).TowerComplete T K := by
  let d := datum.{u} l E π hπ
  constructor
  · rintro ⟨hp, δ, hδ⟩
    let := hp
    obtain ⟨ε, hε⟩ := completedRlim_roos T d ((completedReductionTower T d).obj K)
    obtain ⟨e⟩ := roos_object_iso _ hδ hε
    exact unit_of_iso_completion T d K e
  · intro hK
    have : IsIso (d.completionUnit T K) := hK
    have := quotient_products T d
    obtain ⟨δ, hδ⟩ := completedRlim_roos T d ((completedReductionTower T d).obj K)
    let e := asIso (d.completionUnit T K)
    refine ⟨inferInstance, δ ≫ (shiftFunctor _ (1 : ℤ)).map e.inv, ?_⟩
    apply Pretriangulated.isomorphic_distinguished _ hδ _
    exact Pretriangulated.Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
      (by change (_ ≫ _) ≫ 𝟙 _ = e.hom ≫ _; simp [e, d])
      (by change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
          simp only [Category.comp_id, Category.id_comp]
          rfl)
      (by change (δ ≫ _) ≫ _ = 𝟙 _ ≫ δ
          simp only [Category.assoc, ← Functor.map_comp, e.inv_hom_id, Category.id_comp]
          change δ ≫ (shiftFunctor (d.derived T) (1 : ℤ)).map (𝟙 _) = δ
          simp only [CategoryTheory.Functor.map_id, Category.comp_id])

/-- The ordinary direct image preserves completeness and compares to one strict
finite reduction tower, with its coefficient-linear evaluations and augmentation.
Source: Bhatt--Scholze, Lemma 6.5.9(2),(3); Stacks 0A07 and 099N
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: (1) Arithmetic and finiteResolution give the Noetherian adic hypotheses,
finite l-primary quotients and their two-term free resolutions.
(2) coefficientModel_exists identifies the condensed coefficients with the adic
datum, preserving constants and all quotient projections; cartesian coefficients
give the canonical inverse-image isomorphisms. encodings identifies the ordinary
ambient K-injective direct image, with its action, with d.push.
(3) The perfect projection formula and the scalar-change adjunction produce the
actual P_n-linear finiteProjection isomorphisms. Restriction is conservative.
(4) Apply the reduction/pullback comparison to the ambient counit and transpose
under the strict tower adjunction. Its evaluated arrows are precisely those finite
projections; their tensor formulas commute with every quotient transition. This
is d.towerProjection, with evaluation normalized by towerPushReductionEvaluation.
(5) The augmented projection mate identifies its completion composite with direct
image of the original quotient unit followed by the projection-normalized Rlim
comparison. complete_iff converts the Roos input condition to invertibility of
that unit. The strict map and Rlim comparison are isomorphisms, so the ordinary
pushforward unit is invertible. complete_iff on Y gives its Roos completeness.
The final equality asserts the canonical completion map, not a bare isomorphism
to the same object. All of this is unbounded and uses no properness or origin data. -/
theorem comparison (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : (datum.{u} l E π hπ).derived X)
    (hK : (datum.{u} l E π hπ).quotientRoosComplete X K) :
    (datum.{u} l E π hπ).quotientRoosComplete Y (((datum.{u} l E π hπ).push f).obj K) ∧
      (∀ n : ℕ, IsIso ((datum.{u} l E π hπ).finiteProjection f K n)) ∧
      IsIso ((datum.{u} l E π hπ).towerProjection f K) ∧
      (∀ n : ℕ,
        (reductionTowerDerivedEvaluation Y
            (reductionModuleRing Y ((datum.{u} l E π hπ).completedRing Y)) n).map
              ((datum.{u} l E π hπ).towerProjection f K) ≫
            (datum.{u} l E π hπ).towerPushReductionEvaluation f K n =
          (completedReductionEvaluation Y (datum.{u} l E π hπ) n).app
              (((datum.{u} l E π hπ).push f).obj K) ≫
            (reductionDerivedRestrict Y ((datum.{u} l E π hπ).projection Y n)).map
              ((datum.{u} l E π hπ).finiteProjection f K n)) ∧
      IsIso ((datum.{u} l E π hπ).completionUnit Y (((datum.{u} l E π hπ).push f).obj K) ≫
        (completedRlim Y ((datum.{u} l E π hπ).completedRing Y)).map
            ((datum.{u} l E π hπ).towerProjection f K)) ∧
      (datum.{u} l E π hπ).completionUnit Y (((datum.{u} l E π hπ).push f).obj K) ≫
          (completedRlim Y ((datum.{u} l E π hπ).completedRing Y)).map
            ((datum.{u} l E π hπ).towerProjection f K) =
        ((datum.{u} l E π hπ).push f).map ((datum.{u} l E π hπ).completionUnit X K) ≫
          ((datum.{u} l E π hπ).directImageRlimIso f).hom.app
            ((completedReductionTower X (datum.{u} l E π hπ)).obj K) := by
  let d := datum.{u} l E π hπ
  have h := d.push_complete f K ((complete_iff l E π hπ X K).mp hK)
  have : IsIso (d.completionUnit Y ((d.push f).obj K)) := h
  refine ⟨(complete_iff l E π hπ Y _).mpr h, ?_, inferInstance,
    (d.towerProjection_properties f K).1, inferInstance,
    (d.towerProjection_properties f K).2.2⟩
  intro n
  infer_instance



/-- The recorded comparison inverse image in its fixed-scalar localization.
This is a typed specialization of the existing exact derived functor.
Source: Bhatt--Scholze, Lemma 5.4.3; Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def etalePullback (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategory.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.{u + 1} (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The recorded total direct image in its fixed-scalar localization.
This caches its actual ambient category and imposes no completion.
Source: Bhatt--Scholze, Lemma 5.4.3; Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def proEtalePush (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.{u + 1} (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory.{u + 1} (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- The inverse of the actual bounded-below etale/pro-etale direct-image mate.
Only the proof of its invertibility comes from the published bounded-below theorem;
the arrow is the inverse of that exact mate, not an independently chosen comparison.
Source: Bhatt--Scholze, Lemma 5.4.3; Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def etaleComparisonInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (b : ℤ) [L.IsGE b] :
    (Functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj
        ((Functor.mapDerivedCategory.{u + 1, u + 1}
          (comparisonUpperStar (ModuleCat.{u + 1} A) X)).obj L) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.{u + 1, u + 1}.obj
        ((Functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
          (Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj L) :=
  inv (I := unboundedDirectImageComparison_boundedBelow A f L b)
    (unboundedDirectImageComparisonMap A f L)

/-- The optional finite-level etale-origin clause, with the actual reduction and
normalized finite pushforward square. All antecedents and isomorphisms are retained.
Source: Bhatt--Scholze, Lemma 5.4.3 and Lemma 6.5.9(3)
(blueprint: lem-sfb-integral-ambient-tower-comparison). -/
def FiniteEtaleOriginComparison {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : d.derived X) : Prop :=
  ∀ (n : ℕ)
    (H : FiniteCoefficientPushEncoding d f n)
    (L : DerivedCategory.Plus.{u + 1} (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)))))
    (b : ℤ) [L.obj.IsGE b]
    (θ : (@finiteDerivedFixed.{u} X
        (A ⧸ d.ideal ^ (n + 1)) inferInstance
        (d.quotientFinite n)).obj
          ((d.reduction X n).obj K) ≅
      (etalePullback
        (A ⧸ d.ideal ^ (n + 1)) X).obj
          L.obj),
    IsIso ((FiniteCoefficientPushEncoding.comparison d
        (X := X) (Y := Y) (f := f) (n := n) H).hom.app
          ((d.reduction X n).obj K) ≫
        (proEtalePush
          (A ⧸ d.ideal ^ (n + 1)) f).map
            θ.hom ≫
        @etaleComparisonInverse.{u}
          (A ⧸ d.ideal ^ (n + 1)) inferInstance
          (d.quotientFinite n) X Y f inferInstance inferInstance
          L.obj b inferInstance)

/-- The optional etale antecedent gives the canonical finite-level derived isomorphism,
in the same ringed coefficient coordinates as the integral comparison. Its map is the
normalized finite pushforward encoding, followed by direct image of the specified theta,
followed by the inverse of the actual etale/pro-etale comparison mate.
Source: Bhatt--Scholze, Lemma 5.4.3 and Lemma 6.5.9(3); Stacks 09A6
(blueprint: lem-sfb-integral-ambient-tower-comparison).
Proof: the quotient is finite by arithmetic. Regard the given bounded-below antecedent
as an unbounded etale object. Apply lem-sfb-unbounded-direct-image-bounded-below to its
specified lower bound; this makes the canonical comparison mate invertible. Apply the
ordinary total pro-etale direct image to theta, then compose with that inverse.
FinitePushEncoding.comparison transports the source from the actual ringed finite
pushforward and is normalized by the same ordinary section maps and derived units.
The three factors are isomorphisms, so their prescribed composite is invertible
in the derived category, giving the required canonical derived isomorphism.
No compatibility between antecedents at different levels is used. -/
theorem etaleOriginComparison (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : (datum.{u} l E π hπ).derived X) :
    FiniteEtaleOriginComparison (datum.{u} l E π hπ) f K := by
  intro n H L b hb θ
  let A := integers.{u} l E ⧸ (datum.{u} l E π hπ).ideal ^ (n + 1)
  have : Finite A := (datum.{u} l E π hπ).quotientFinite n
  have hm : IsIso (unboundedDirectImageComparisonMap A f L.obj) :=
    unboundedDirectImageComparison_boundedBelow A f L.obj b
  have hθ : IsIso ((proEtalePush A f).map θ.hom) := by infer_instance
  dsimp only [etaleComparisonInverse]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hθ inferInstance)

end AlgebraicGeometry.Scheme.IntegralAmbientTower
