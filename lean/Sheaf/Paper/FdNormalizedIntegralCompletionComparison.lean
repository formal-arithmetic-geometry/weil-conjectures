module

public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedScalarChainShift
public import Sheaf.Paper.CompletedScalarShift
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.Paper.CompletedScalarShiftDescent
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.QuotientScalarComparisonDescent
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

import Sheaf.Paper.CompletedScalarOrdinaryNormalizedExact
import Sheaf.Paper.FdCoefficientScalarLiftNormalization
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

/-! # Normalized exact integral completion comparison

Source: main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function,
final coefficient-category sentence; Bhatt--Scholze, Definition 3.4.10,
Lemma 3.4.12, Proposition 3.5.1 and Lemma 6.8.2.
(blueprint: lem-fd-normalized-integral-completion-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (T : Scheme.{u})

/-- Restrict ordinary derived tensor to the actual integral full subcategories.
The supplied proof is only membership, not a replacement scalar functor.
Source: trace-definition coefficient comparison, restriction step
(blueprint: lem-fd-normalized-integral-completion-comparison). -/
def fdIntegralOrdinaryRestriction
    (hC : ∀ K, sfIntegralConstructible l E T K →
      sfIntegralConstructible l L T ((completedDerivedScalarExtension l E L ι T).obj K)) :=
  (sfIntegralConstructible l E T).liftFullSubcategory (sfIntegralConstructible l L T)
    (completedDerivedScalarExtension l E L ι T) hC

/-- Restrict the recorded strict quotient-tower functor, leaving every morphism unchanged.
Source: trace-definition coefficient comparison, restriction step
(blueprint: lem-fd-normalized-integral-completion-comparison). -/
def fdIntegralStrictRestriction
    (hU : ∀ K, sfIntegralConstructible l E T K →
      sfIntegralConstructible l L T ((integralScalarExtensionOfUniverses l E L ι T).obj K)) :=
  (sfIntegralConstructible l E T).liftFullSubcategory (sfIntegralConstructible l L T)
    (integralScalarExtensionOfUniverses l E L ι T) hU

/-- The quotient-normalized completion comparison and its inverse restrict to exact
integral functors with the specified, rather than transported, shifts.
Source: trace-definition coefficient-category sentence; Bhatt--Scholze 3.4.10,
3.4.12, 3.5.1 and 6.8.2
(blueprint: lem-fd-normalized-integral-completion-comparison).

Proof:
1. Integral stratified-perfect characterization identifies the two integral full
categories through integralDetailedTransport. Their shifts and triangles are inherited.
Strict scalar extension preserves constructibility. Every integral object is complete,
so finiteFreeCompletedScalarComparison makes its actual chi invertible. Isomorphism
closure gives ordinary scalar preservation; fullness restricts chi and its inverse.
2. Ordinary coefficient-presentation transport fixes the sheafified tensor generators.
The inverse transport reverses the normalized coefficient isomorphism, so the two
composites fix generators and are identities by the balanced tensor universal property.
3. Countable products on the pro-etale site are exact. Quotient-scalar comparison
descent gives precisely the actual quotient coordinates and zero second coordinate.
Its canonical resolving comparisons give the displayed localization equation, independent
of the representative. Composing the ordinary transport with this map gives exactly the
integral lift in FdCoefficientComparison. For equal fields multiplication identifies it
with the natural completeness unit.
4. CompletedScalarChainShift gives (x,y) ↦ (x,(-1)^m y) with the specified product
shift. It fixes (c(z),0). CompletedScalarShiftDescent conjugates this chain equation
by the retained resolving comparisons. Their cancellation gives the shift square for chi.
5. Invert its components to obtain the inverse shift square for every integer m.
Ordinary derived tensor is exact. Naturality supplies the first two triangle squares;
the shift square supplies the closing square. The isomorphism axiom transfers
exactness to strict extension, with these same shifts. Fullness restricts both squares
and the image triangles. This proves exactness of both natural isomorphisms.
-/
theorem fdNormalizedIntegralCompletionComparison
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    [IsNoetherian T] [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    ∃ (eChain : (integralScalarComplexFunctor l E L ι T).CommShift ℤ)
      (eOrd : (completedDerivedScalarExtension l E L ι T).CommShift ℤ)
      (eStrict : (integralScalarExtensionOfUniverses l E L ι T).CommShift ℤ),
    completedScalarShiftRepresentativeProperty ι T eChain eOrd eStrict ∧
    ∃ (hC : ∀ K, sfIntegralConstructible l E T K →
        sfIntegralConstructible l L T ((completedDerivedScalarExtension l E L ι T).obj K))
      (hU : ∀ K, sfIntegralConstructible l E T K →
        sfIntegralConstructible l L T
          ((integralScalarExtensionOfUniverses l E L ι T).obj K))
      (b : fdIntegralOrdinaryRestriction l E L ι T hC ≅
        fdIntegralStrictRestriction l E L ι T hU)
      (sC : (fdIntegralOrdinaryRestriction l E L ι T hC).CommShift ℤ)
      (sU : (fdIntegralStrictRestriction l E L ι T hU).CommShift ℤ),
    (∀ K, (b.hom.app K).hom = (completedScalarComparison l E L ι T).app K.obj) ∧
    (fun [_s : (fdIntegralOrdinaryRestriction l E L ι T hC).CommShift ℤ] ↦
      (fdIntegralOrdinaryRestriction l E L ι T hC).IsTriangulated) (_s := sC) ∧
    (fun [_s : (fdIntegralStrictRestriction l E L ι T hU).CommShift ℤ] ↦
      (fdIntegralStrictRestriction l E L ι T hU).IsTriangulated) (_s := sU) ∧
    (fun [_sC : (fdIntegralOrdinaryRestriction l E L ι T hC).CommShift ℤ]
      [_sU : (fdIntegralStrictRestriction l E L ι T hU).CommShift ℤ] ↦
      NatTrans.CommShift b.hom ℤ ∧ NatTrans.CommShift b.inv ℤ)
        (_sC := sC) (_sU := sU) ∧
    (∀ (m : ℤ) K,
      HEq (((sfIntegralConstructible l L T).ι).map
          ((Functor.commShiftIso _ (self := sC) m).hom.app K) ≫
        (((sfIntegralConstructible l L T).ι).commShiftIso m).hom.app
          ((fdIntegralOrdinaryRestriction l E L ι T hC).obj K))
        ((completedDerivedScalarExtension l E L ι T).map
          ((((sfIntegralConstructible l E T).ι).commShiftIso m).hom.app K) ≫
        (Functor.commShiftIso _ (self := eOrd) m).hom.app K.obj)) ∧
    (∀ (m : ℤ) K,
      HEq (((sfIntegralConstructible l L T).ι).map
          ((Functor.commShiftIso _ (self := sU) m).hom.app K) ≫
        (((sfIntegralConstructible l L T).ι).commShiftIso m).hom.app
          ((fdIntegralStrictRestriction l E L ι T hU).obj K))
        ((integralScalarExtensionOfUniverses l E L ι T).map
          ((((sfIntegralConstructible l E T).ι).commShiftIso m).hom.app K) ≫
        (Functor.commShiftIso _ (self := eStrict) m).hom.app K.obj)) ∧
    (∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
      (completedScalarComparison l E L ι T).app (DerivedCategory.Q.obj P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses l E L ι T).hom.app P =
        completedScalarCounit l E L ι T P.obj ≫
          DerivedCategory.Q.map ((completedScalarChainComparison l E L ι T).app P.obj)) ∧
    (∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory) (i : ℤ)
      (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L T).obj.obj U)
      (x : (P.obj.X i).val.obj U),
      ((((completedScalarChainComparison l E L ι T).app P.obj).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι T P.obj)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι T).obj P.obj).obj (op n)) n).f
          i).val.app U) (completedScalarTensorSection l E L ι T (P.obj.X i) U s x) =
        integralScalarTensorSection l E L ι T n (P.obj.X i) U
          ((completedIntegralCommRingProjectionUnrestricted l L T n).hom.app U s) x) ∧
    (∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory) (i : ℤ),
      ((completedScalarChainComparison l E L ι T).app P.obj).f i ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E L ι T P.obj)).v i (i - 1) (by omega) = 0) ∧
    (∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
      (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) T).app
          (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E) T).hom.app P =
      completedScalarCounit l E E (AlgHom.id ℚ_[l] E) T P.obj ≫
        DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E T).hom.app P.obj) ≫
        DerivedCategory.Q.map ((completedScalarIdentityUnit l E T).app P.obj)) ∧
    (∀ {A B : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B),
      ∃ (o : FdOrdinaryScalarTransport l Ω T h)
        (a : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω A) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω A) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        sfConstructibleIntegralScalarExtension D.p l hl (pbcFiniteField.{u} l Ω A)
          (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω B) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)),
      ∀ (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω A) T).FullSubcategory)
        (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω A) T
          (DerivedCategory.Q.obj P.obj)),
      HEq (a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω A)
            (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω B) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω A)
            (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω A) T).hom.app P.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω A) T).mapHomologicalComplex
            (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map (o.completion l Ω P.obj))) := by
  classical
  obtain ⟨eChain, eOrd, eStrict, hrep⟩ :=
    completedScalarComparison_commutesWithShift l E L ι T
  let := eOrd
  let := eStrict
  have hχ : NatTrans.CommShift (completedScalarComparison l E L ι T) ℤ := hrep.2.2.2.2
  let := hχ
  have hOrd : (completedDerivedScalarExtension l E L ι T).IsTriangulated :=
    completedScalarOrdinary_normalized_exact l E L ι T eOrd hrep.2.2.1
  let := hOrd
  have hiso (K) (hK : sfIntegralConstructible l E T K) :
      IsIso ((completedScalarComparison l E L ι T).app K) := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1
        cardinality_eq := (pow_one p).symm, k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
    exact ((finiteFreeCompletedScalarComparison l E L ι T).2.1 K
      ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E T D₀ hl₀ K).mp hK.1⟩).1
  let hU : ∀ K, sfIntegralConstructible l E T K →
      sfIntegralConstructible l L T
        ((integralScalarExtensionOfUniverses l E L ι T).obj K) :=
    fun K hK ↦ sfIntegralScalarExtension_constructible D.p l hl E L ι T K hK
  let hC : ∀ K, sfIntegralConstructible l E T K →
      sfIntegralConstructible l L T ((completedDerivedScalarExtension l E L ι T).obj K) := by
    intro K hK
    have := hiso K hK
    exact (sfIntegralConstructible l L T).prop_of_iso
      (asIso ((completedScalarComparison l E L ι T).app K)).symm (hU K hK)
  let F := fdIntegralOrdinaryRestriction l E L ι T hC
  let G := fdIntegralStrictRestriction l E L ι T hU
  let iF : F ⋙ (sfIntegralConstructible l L T).ι ≅
      (sfIntegralConstructible l E T).ι ⋙ completedDerivedScalarExtension l E L ι T :=
    (sfIntegralConstructible l E T).liftFullSubcategoryCompιIso
      (sfIntegralConstructible l L T) _ hC
  let iG : G ⋙ (sfIntegralConstructible l L T).ι ≅
      (sfIntegralConstructible l E T).ι ⋙ integralScalarExtensionOfUniverses l E L ι T :=
    (sfIntegralConstructible l E T).liftFullSubcategoryCompιIso
      (sfIntegralConstructible l L T) _ hU
  let sC : F.CommShift ℤ := Functor.CommShift.ofComp iF ℤ
  let sU : G.CommShift ℤ := Functor.CommShift.ofComp iG ℤ
  let := sC
  let := sU
  have hiF : NatTrans.CommShift iF.hom ℤ := Functor.CommShift.ofComp_compatibility iF ℤ
  have hiG : NatTrans.CommShift iG.hom ℤ := Functor.CommShift.ofComp_compatibility iG ℤ
  let := hiF
  let := hiG
  have hSC (m : ℤ) (K) :
      (sfIntegralConstructible l L T).ι.map ((F.commShiftIso m).hom.app K) ≫
        ((sfIntegralConstructible l L T).ι.commShiftIso m).hom.app (F.obj K) =
      (completedDerivedScalarExtension l E L ι T).map
        (((sfIntegralConstructible l E T).ι.commShiftIso m).hom.app K) ≫
        (Functor.commShiftIso _ (self := eOrd) m).hom.app K.obj := by
    have h := NatTrans.shift_app_comm iF.hom m K
    dsimp only [F, fdIntegralOrdinaryRestriction] at h ⊢
    simpa only [Functor.commShiftIso_comp_hom_app, iF, F, fdIntegralOrdinaryRestriction,
      ObjectProperty.liftFullSubcategoryCompιIso, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.liftFullSubcategory,
      ObjectProperty.lift_obj_obj, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp] using h
  have hSU (m : ℤ) (K) :
      (sfIntegralConstructible l L T).ι.map ((G.commShiftIso m).hom.app K) ≫
        ((sfIntegralConstructible l L T).ι.commShiftIso m).hom.app (G.obj K) =
      (integralScalarExtensionOfUniverses l E L ι T).map
        (((sfIntegralConstructible l E T).ι.commShiftIso m).hom.app K) ≫
        (Functor.commShiftIso _ (self := eStrict) m).hom.app K.obj := by
    have h := NatTrans.shift_app_comm iG.hom m K
    dsimp only [G, fdIntegralStrictRestriction] at h ⊢
    simpa only [Functor.commShiftIso_comp_hom_app, iG, G, fdIntegralStrictRestriction,
      ObjectProperty.liftFullSubcategoryCompιIso, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.liftFullSubcategory,
      ObjectProperty.lift_obj_obj, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp] using h
  let b : F ≅ G := NatIso.ofComponents (fun K ↦ by
    have := hiso K.obj K.property
    exact (sfIntegralConstructible l L T).isoMk
      (asIso ((completedScalarComparison l E L ι T).app K.obj)))
    (by
      intro K K' f
      exact (sfIntegralConstructible l L T).hom_ext
        ((completedScalarComparison l E L ι T).naturality f.hom))
  have hb : NatTrans.CommShift b.hom ℤ := by
    constructor
    intro m
    apply NatTrans.ext
    funext K
    apply (sfIntegralConstructible l L T).ι.map_injective
    apply (cancel_mono
      (((sfIntegralConstructible l L T).ι.commShiftIso m).hom.app (G.obj K))).mp
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.map_comp, Category.assoc]
    have hn := ((sfIntegralConstructible l L T).ι.commShiftIso m).hom.naturality
      (b.hom.app K)
    simp only [Functor.comp_map] at hn
    rw [hn]
    rw [← Category.assoc, hSC, Category.assoc, hSU]
    change (completedDerivedScalarExtension l E L ι T).map _ ≫
        ((Functor.commShiftIso _ (self := eOrd) m).hom.app K.obj ≫
          ((completedScalarComparison l E L ι T).app K.obj)⟦m⟧') =
      (completedScalarComparison l E L ι T).app _ ≫
        ((integralScalarExtensionOfUniverses l E L ι T).map _ ≫
          (Functor.commShiftIso _ (self := eStrict) m).hom.app K.obj)
    rw [NatTrans.shift_app_comm, ← Category.assoc,
      (completedScalarComparison l E L ι T).naturality]
    simp only [Category.assoc]
  let := hb
  have hF : F.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right iF).2 inferInstance
  let := hF
  have hG : G.IsTriangulated := Functor.isTriangulated_of_iso b
  refine ⟨eChain, eOrd, eStrict, hrep, hC, hU, b, sC, sU,
    (fun _ ↦ rfl), hF, hG, ⟨hb, inferInstance⟩,
    (fun m K ↦ heq_of_eq (hSC m K)), (fun m K ↦ heq_of_eq (hSU m K)),
    ?_, ?_, ?_, (finiteFreeCompletedScalarComparison l E L ι T).2.2,
    fdCoefficientScalarLift_normalization l D hl Ω T⟩
  · exact (completedScalarComparison_existsUnique l E L ι T).exists.choose_spec
  · intro P i n U s x
    exact (completedScalarChainComparison_existsUnique l E L ι T).exists.choose_spec.1
      P.obj i n U s x
  · intro P i
    exact (completedScalarChainComparison_existsUnique l E L ι T).exists.choose_spec.2
      P.obj i

end WeilConjectures
