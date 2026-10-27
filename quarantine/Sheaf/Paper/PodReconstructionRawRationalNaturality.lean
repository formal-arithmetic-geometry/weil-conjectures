/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.PodIdentityReductionTower
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.CompletionUnitStrictQuotientModel
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.Paper.PodCompletionUnitScalarIntertwining
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
import all Sheaf.Paper.CompactSupportReductionTower
import all Sheaf.Paper.CompactSupportRepresentativeIndependence
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.SfIntegralConstructibleLinear
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.CompactSupportNormalizedTowerLimit

/-! # Actual reconstruction on raw rational Hom groups

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, first sentence; Bhatt--Scholze,
Definitions 3.5.2--3.5.3, Lemmas 3.5.7 and 6.8.2(1).
(blueprint: lem-pod-reconstruction-raw-rational-naturality).

The functors below use the existing full constructible categories and raw tensor-Hom
localizations. The realization predicates prescribe objects and every morphism,
so the existence assertions do not select arbitrary functors or comparison maps.
Main declarations: IntegralRealization, RationalRealization,
reconstructionRawRationalNaturality, finiteOpenIdentity, finiteIdentity,
finiteRestrictedIdentity, and reconstruction_identityCompactSupport.

The site has object universe u+1 and morphism universe u; module coefficients have
universe u+1. The natural index n is the positive quotient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard
attribute [instance 5000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
  AlgebraicGeometry.Scheme TensorProduct

namespace WeilConjectures.PodRawReconstruction
open PodCompletionScalar

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Restriction of the actual quotient-system reconstruction, literally on underlying
objects and arrows, and the actual unit and its inverse. HEq only transports the
endpoints specified by the object equality; it does not forget the arrow.
Source: blueprint opening sentence, reconstruction restriction
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def IntegralRealization (A : CoefficientDerivedSystemCalculus l E (point D))
    (H : sfIntegralConstructibleCategory l E (point D) ⥤
      sfIntegralConstructibleCategory l E (point D))
    (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H) : Prop :=
  (∀ C, (H.obj C).obj = (completion.{u, u} D l E A).obj C.obj) ∧
  (∀ (C C' : sfIntegralConstructibleCategory l E (point D)) (f : C ⟶ C'),
    HEq (H.map f).hom ((completion.{u, u} D l E A).map f.hom)) ∧
  ∀ C, HEq (unit.hom.app C).hom (A.adjunction.unit.app C.obj)

/-- Raw rationalization of precisely the integral endofunctor and its two components.
The tensor formula is in the library's scalar-first coordinates; the canonical
sfRationalHomCoordinates changes it to Hom tensor E, as in the node.
Source: blueprint opening sentence, raw rational descent
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def RationalRealization
    (H : sfIntegralConstructibleCategory l E (point D) ⥤
      sfIntegralConstructibleCategory l E (point D))
    (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H)
    (J : sfRationalConstructibleCategory l E (point D) ⥤
      sfRationalConstructibleCategory l E (point D))
    (unitRat : 𝟭 (sfRationalConstructibleCategory l E (point D)) ≅ J) : Prop :=
  J.Linear (Localization.Away (Padic.coefficientExtensionUniformizer l E)) ∧
  J.Additive ∧
  (∀ C : sfRationalConstructibleCategory l E (point D), J.obj C = ⟨H.obj C.obj⟩) ∧
  (∀ (C C' : sfIntegralConstructibleCategory l E (point D)) (f : C ⟶ C')
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq (J.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
      (sfRationalConstructibleLocalization l E (point D)).obj C ⟶
        (sfRationalConstructibleLocalization l E (point D)).obj C'))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] H.map f :
        (sfRationalConstructibleLocalization l E (point D)).obj (H.obj C) ⟶
          (sfRationalConstructibleLocalization l E (point D)).obj (H.obj C'))) ∧
  (∀ C : sfRationalConstructibleCategory l E (point D),
    HEq (unitRat.hom.app C)
        ((sfRationalConstructibleLocalization l E (point D)).map (unit.hom.app C.obj)) ∧
      HEq (unitRat.inv.app C)
        ((sfRationalConstructibleLocalization l E (point D)).map (unit.inv.app C.obj))) ∧
  ∀ (C C' : sfRationalConstructibleCategory l E (point D)) (h : C ⟶ C'),
    J.map h ≫ unitRat.inv.app C' = unitRat.inv.app C ≫ h ∧
      unitRat.hom.app C ≫ J.map h = h ≫ unitRat.hom.app C'

private theorem completion_linear (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (A : CoefficientDerivedSystemCalculus l E (point D)) :
    (completion.{u, u} D l E A).Linear (Padic.coefficientExtensionIntegers l E) := by
  let W := point D
  let R := Padic.coefficientExtensionIntegers l E
  let := compactSupportScalarLinear l E W
  let := compactSupportSequenceLinear l E W
  let := DerivedCategory.instLinear R (scalarReductionSource l E W)
  let := DerivedCategory.instLinear R (coefficientSequenceModules l E W)
  let := DerivedCategory.instLinear R (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  have := compactSupportSequenceRestrictionLinear l E W
  have := compactSupportLimitLinear l E W
  have : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctor.Linear R :=
    compactSupportRightDerivedLinear _ _
  have : (coefficientSequenceLimit l E W).Linear R := by
    unfold coefficientSequenceLimit coefficientConstantTowerLimit
      coefficientSequenceDerivedRestriction
    infer_instance
  have : A.reduction.Linear R := A.adjunction.left_adjoint_linear
  have h : (completion D l E A).Linear R := inferInstance
  change @Functor.Linear R _ _ _ _ _ _ _
    (DerivedCategory.instLinear R (scalarReductionSource l E W))
    (DerivedCategory.instLinear R (scalarReductionSource l E W)) (completion D l E A) at h
  rw [normalizedDerivedLinear l E W (compactSupportScalarLinear l E W)
    (compactSupportScalarLinear_normalized l E W)] at h
  exact h


private theorem map_heq {C C' : Type*} [Category C] [Category C']
    (F : C ⥤ C') {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

private theorem comp_heq {C : Type*} [Category C] {X Y Z X' Y' Z' : C}
    (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst X'; subst Y'; subst Z'
  exact heq_of_eq (congrArg₂ (· ≫ ·) (eq_of_heq hf) (eq_of_heq hg))

private theorem integralRestriction (hl : l ≠ D.p)
    (A : CoefficientDerivedSystemCalculus l E (point D)) :
    ∃ (H : sfIntegralConstructibleCategory l E (point D) ⥤
        sfIntegralConstructibleCategory l E (point D))
      (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H),
      IntegralRealization D l E A H unit ∧
        H.Linear (Padic.coefficientExtensionIntegers l E) := by
  let P := sfIntegralConstructible l E (point D)
  have hi (C : sfIntegralConstructibleCategory l E (point D)) :
      IsIso (A.adjunction.unit.app C.obj) := by
    apply (purNormalizedReconstructionOfScheme l E (point D) A).2
    let : Fact D.p.Prime := ⟨D.prime⟩
    let Δ : FiniteFieldDatum.{0} := {
      p := D.p, a := 1, q := D.p, prime := D.prime, exponent_pos := le_refl 1,
      cardinality_eq := (pow_one D.p).symm, k₀ := ZMod D.p,
      card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod D.p) }
    exact ⟨Δ, hl, (sfDerivedComplete_iff_legacy l E (point D) Δ hl C.obj).mp
      C.property.1⟩
  let e (C : sfIntegralConstructibleCategory l E (point D)) :=
    @asIso _ _ _ _ (A.adjunction.unit.app C.obj) (hi C)
  let H := P.lift (P.ι ⋙ completion D l E A)
    (fun C ↦ P.prop_of_iso (e C) C.property)
  let unit : 𝟭 _ ≅ H := NatIso.ofComponents
    (fun C ↦ P.isoMk (e C)) (fun {C C'} f ↦ by
      apply ObjectProperty.hom_ext
      exact A.adjunction.unit.naturality f.hom)
  refine ⟨H, unit, ⟨fun _ ↦ rfl, fun _ _ _ ↦ HEq.rfl, fun _ ↦ HEq.rfl⟩, ?_⟩
  exact Functor.linear_of_iso (Padic.coefficientExtensionIntegers l E) unit

private theorem rationalRestriction
    (H : sfIntegralConstructibleCategory l E (point D) ⥤
      sfIntegralConstructibleCategory l E (point D))
    (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H)
    [H.Linear (Padic.coefficientExtensionIntegers l E)] :
    ∃ (J : sfRationalConstructibleCategory l E (point D) ⥤
        sfRationalConstructibleCategory l E (point D))
      (unitRat : 𝟭 (sfRationalConstructibleCategory l E (point D)) ≅ J),
      RationalRealization D l E H unit J unitRat := by
  let R := Padic.coefficientExtensionIntegers l E
  let C := sfIntegralConstructibleCategory l E (point D)
  let t := Padic.coefficientExtensionUniformizer l E
  have : H.Additive := Functor.additive_of_iso unit
  let J := ScalarLocalization.map R C t H
  let Q := sfRationalConstructibleLocalization l E (point D)
  have hn (K M : sfRationalConstructibleCategory l E (point D)) (f : K ⟶ M) :
      f ≫ Q.map (unit.hom.app M.obj) = Q.map (unit.hom.app K.obj) ≫ J.map f := by
    rcases K with ⟨K⟩
    rcases M with ⟨M⟩
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      change ScalarLocalization.composition R C t _ _ _ (1 ⊗ₜ[R] unit.hom.app M)
        (a ⊗ₜ[R] f) = ScalarLocalization.composition R C t _ _ _
          (ScalarLocalization.mapHom R C t H _ _ (a ⊗ₜ[R] f))
          (1 ⊗ₜ[R] unit.hom.app K)
      simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul,
        ScalarLocalization.composition_tmul, one_mul, mul_one]
      exact congrArg (fun g ↦ a ⊗ₜ[R] g) (unit.hom.naturality f)
    | add f g hf hg =>
      change ScalarLocalization.composition R C t K M (H.obj M)
        (1 ⊗ₜ[R] unit.hom.app M) f =
          ScalarLocalization.composition R C t K (H.obj K) (H.obj M)
            (ScalarLocalization.mapHom R C t H K M f)
            (1 ⊗ₜ[R] unit.hom.app K) at hf
      change ScalarLocalization.composition R C t K M (H.obj M)
        (1 ⊗ₜ[R] unit.hom.app M) g =
          ScalarLocalization.composition R C t K (H.obj K) (H.obj M)
            (ScalarLocalization.mapHom R C t H K M g)
            (1 ⊗ₜ[R] unit.hom.app K) at hg
      change ScalarLocalization.composition R C t K M (H.obj M)
        (1 ⊗ₜ[R] unit.hom.app M) (f + g) =
          ScalarLocalization.composition R C t K (H.obj K) (H.obj M)
            (ScalarLocalization.mapHom R C t H K M (f + g))
            (1 ⊗ₜ[R] unit.hom.app K)
      simp only [_root_.map_add, LinearMap.add_apply, hf, hg]
  let unitRat : 𝟭 _ ≅ J := NatIso.ofComponents
    (fun K ↦ Q.mapIso (unit.app K.obj)) (fun {K M} f ↦ hn K M f)
  refine ⟨J, unitRat, inferInstance, inferInstance, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · intro K M f a
    apply heq_of_eq
    change (H.mapLinearMap R).baseChange (Localization.Away t) (a ⊗ₜ[R] f) = _
    exact LinearMap.baseChange_tmul _ _ _
  · intro K
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro K M f
    exact ⟨unitRat.inv.naturality f, (unitRat.hom.naturality f).symm⟩

/-- Reconstruction is linear, restricts to the full constructible category, and its
actual unit and inverse descend on every raw rational morphism. The scalar square
uses the specified completed integral extension and its recorded rationalization.
Source: blueprint opening sentence; Bhatt--Scholze 3.5.2--3.5.3, 3.5.7, 6.8.2(1)
(blueprint: lem-pod-reconstruction-raw-rational-naturality).

Proof (DAG steps 1, 2, 4, 5, 6; the identity-tower clause is stated separately):
1. Strict-system restriction and limit carry the constant-section linear actions.
Their right-derived functors are linear. Adjoint linearity gives linear reduction,
so completion is linear. The normalized derived-action comparison identifies this
with the published integral action.
2. Convert intrinsic completeness to legacy completeness using the prime-field datum
in universe zero. Normalized reconstruction makes the actual unit invertible there.
Closure under isomorphisms preserves constructibility; lift the actual completion
and unit to the full constructible subcategory. The unit also gives linearity.
3. ScalarLocalization.map tensors the integral linear Hom maps with the localized
field, with the same objects. Its tensor formula and linearity instances give the
specified raw rational action.
4. Apply Q to the actual unit and its inverse. Integral naturality proves naturality
on pure tensors using the tensor-composition formula. Tensor induction handles zero
and sums, and the natural inverse gives both equations on every rational arrow.
5. Define beta as S(unit inverse) followed by the target unit, and do the same for
betaRat. Cancellation gives the inverse-unit equations; these uniquely characterize
the specified comparisons. The scalar-extension specification at 1 tensor f and
the two unit component formulas identify betaRat with Q_L(beta), with the prescribed
endpoint transports. No integral isomorphism lifts or idempotent summands are used. -/
theorem reconstructionRawRationalNaturality (hl : l ≠ D.p)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (A : CoefficientDerivedSystemCalculus l E (point D))
    (B : CoefficientDerivedSystemCalculus l L (point D)) :
    (completion.{u, u} D l E A).Linear (Padic.coefficientExtensionIntegers l E) ∧
    (completion.{u, u} D l L B).Linear (Padic.coefficientExtensionIntegers l L) ∧
    ∃ (H : sfIntegralConstructibleCategory l E (point D) ⥤
        sfIntegralConstructibleCategory l E (point D))
      (H' : sfIntegralConstructibleCategory l L (point D) ⥤
        sfIntegralConstructibleCategory l L (point D))
      (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H)
      (unit' : 𝟭 (sfIntegralConstructibleCategory l L (point D)) ≅ H'),
      IntegralRealization D l E A H unit ∧ IntegralRealization D l L B H' unit' ∧
      H.Linear (Padic.coefficientExtensionIntegers l E) ∧
      H'.Linear (Padic.coefficientExtensionIntegers l L) ∧
      ∃ (J : sfRationalConstructibleCategory l E (point D) ⥤
          sfRationalConstructibleCategory l E (point D))
        (J' : sfRationalConstructibleCategory l L (point D) ⥤
          sfRationalConstructibleCategory l L (point D))
        (unitRat : 𝟭 (sfRationalConstructibleCategory l E (point D)) ≅ J)
        (unitRat' : 𝟭 (sfRationalConstructibleCategory l L (point D)) ≅ J'),
        RationalRealization D l E H unit J unitRat ∧
        RationalRealization D l L H' unit' J' unitRat' ∧
        ∃ (β : H ⋙ sfConstructibleIntegralScalarExtension D.p l hl E L ι (point D) ≅
            sfConstructibleIntegralScalarExtension D.p l hl E L ι (point D) ⋙ H')
          (βRat : J ⋙ sfRationalScalarExtension l E (point D) D.p hl L ι ≅
            sfRationalScalarExtension l E (point D) D.p hl L ι ⋙ J'),
          (∀ C, β.hom.app C ≫ unit'.inv.app
              ((sfConstructibleIntegralScalarExtension D.p l hl E L ι (point D)).obj C) =
            (sfConstructibleIntegralScalarExtension D.p l hl E L ι (point D)).map
              (unit.inv.app C)) ∧
          (∀ C : sfRationalConstructibleCategory l E (point D),
            HEq (βRat.hom.app C)
              ((sfRationalConstructibleLocalization l L (point D)).map (β.hom.app C.obj))) ∧
          ∀ C : sfRationalConstructibleCategory l E (point D),
            βRat.hom.app C ≫ unitRat'.inv.app
                ((sfRationalScalarExtension l E (point D) D.p hl L ι).obj C) =
              (sfRationalScalarExtension l E (point D) D.p hl L ι).map
                (unitRat.inv.app C) := by
  have hlin := completion_linear D l E A
  have hlin' := completion_linear D l L B
  obtain ⟨H, unit, hH, hHL⟩ := integralRestriction D l E hl A
  obtain ⟨H', unit', hH', hHL'⟩ := integralRestriction D l L hl B
  have := hHL
  have := hHL'
  obtain ⟨J, unitRat, hJ⟩ := rationalRestriction D l E H unit
  obtain ⟨J', unitRat', hJ'⟩ := rationalRestriction D l L H' unit'
  refine ⟨hlin, hlin', H, H', unit, unit', hH, hH', hHL, hHL',
    J, J', unitRat, unitRat', hJ, hJ', ?_⟩
  let S := sfConstructibleIntegralScalarExtension D.p l hl E L ι (point D)
  let Sr := sfRationalScalarExtension l E (point D) D.p hl L ι
  let Q := sfRationalConstructibleLocalization l E (point D)
  let Q' := sfRationalConstructibleLocalization l L (point D)
  let β : H ⋙ S ≅ S ⋙ H' :=
    isoWhiskerRight unit.symm S ≪≫ Functor.leftUnitor S ≪≫
      (Functor.rightUnitor S).symm ≪≫ isoWhiskerLeft S unit'
  let βRat : J ⋙ Sr ≅ Sr ⋙ J' :=
    isoWhiskerRight unitRat.symm Sr ≪≫ Functor.leftUnitor Sr ≪≫
      (Functor.rightUnitor Sr).symm ≪≫ isoWhiskerLeft Sr unitRat'
  have hb (C) : β.hom.app C = S.map (unit.inv.app C) ≫ unit'.hom.app (S.obj C) := by
    simp [β]
  have hbr (C) : βRat.hom.app C =
      Sr.map (unitRat.inv.app C) ≫ unitRat'.hom.app (Sr.obj C) := by
    simp [βRat]
  have hs := (sfRationalScalarExtension_existsUnique l E (point D) D.p hl L ι)
    |>.exists.choose_spec
  have hso (C) : Sr.obj C = ⟨S.obj C.obj⟩ := hs.2.1 C
  have hsm (C C' : sfIntegralConstructibleCategory l E (point D)) (f : C ⟶ C') :
      HEq (Sr.map (Q.map f)) (Q'.map (S.map f)) := by
    have h := hs.2.2 C C' f 1
    change HEq (Sr.map (Q.map f))
      ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E 1))
        ⊗ₜ[Padic.coefficientExtensionIntegers l L] S.map f) at h
    change HEq (Sr.map (Q.map f))
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
        ⊗ₜ[Padic.coefficientExtensionIntegers l L] S.map f)
    simpa only [map_one] using h
  rcases hJ with ⟨_, _, hjo, _, hju, _⟩
  rcases hJ' with ⟨_, _, hjo', _, hju', _⟩
  refine ⟨β, βRat, ?_, ?_, ?_⟩
  · intro C
    change β.hom.app C ≫ unit'.inv.app (S.obj C) = S.map (unit.inv.app C)
    rw [hb, Category.assoc, unit'.hom_inv_id_app]
    exact Category.comp_id _
  · intro C
    rw [hbr, hb, Q'.map_comp]
    have h1 : HEq (Sr.map (unitRat.inv.app C))
        (Q'.map (S.map (unit.inv.app C.obj))) :=
      (map_heq Sr (hjo C) rfl (hju C).2).trans (hsm _ _ _)
    have hu (X Y : sfRationalConstructibleCategory l L (point D)) (h : X = Y) :
        HEq (Q'.map (unit'.hom.app X.obj)) (Q'.map (unit'.hom.app Y.obj)) := by
      subst Y
      rfl
    have h2 := ((hju' (Sr.obj C)).1).trans (hu _ _ (hso C))
    apply comp_heq _ (hso C) _ h1 h2
    · exact (congrArg Sr.obj (hjo C)).trans (hso ⟨H.obj C.obj⟩)
    · exact (hjo' (Sr.obj C)).trans
        (congrArg (fun K : sfRationalConstructibleCategory l L (point D) ↦
          Q'.obj (H'.obj K.obj)) (hso C))
  · intro C
    change βRat.hom.app C ≫ unitRat'.inv.app (Sr.obj C) = Sr.map (unitRat.inv.app C)
    rw [hbr, Category.assoc, unitRat'.hom_inv_id_app]
    exact Category.comp_id _

private theorem localizedUnit
    (H : sfIntegralConstructibleCategory l E (point D) ⥤
      sfIntegralConstructibleCategory l E (point D))
    (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H)
    [H.Additive] [H.Linear (Padic.coefficientExtensionIntegers l E)] :
    ∃ unitRat : 𝟭 (sfRationalConstructibleCategory l E (point D)) ≅
        ScalarLocalization.map (Padic.coefficientExtensionIntegers l E)
          (sfIntegralConstructibleCategory l E (point D))
          (Padic.coefficientExtensionUniformizer l E) H,
      ∀ C : sfRationalConstructibleCategory l E (point D),
        unitRat.hom.app C =
          (sfRationalConstructibleLocalization l E (point D)).map (unit.hom.app C.obj) := by
  let R := Padic.coefficientExtensionIntegers l E
  let C := sfIntegralConstructibleCategory l E (point D)
  let t := Padic.coefficientExtensionUniformizer l E
  let J := ScalarLocalization.map R C t H
  let Q := sfRationalConstructibleLocalization l E (point D)
  have hn (K M : sfRationalConstructibleCategory l E (point D)) (f : K ⟶ M) :
      f ≫ Q.map (unit.hom.app M.obj) = Q.map (unit.hom.app K.obj) ≫ J.map f := by
    rcases K with ⟨K⟩
    rcases M with ⟨M⟩
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      change ScalarLocalization.composition R C t _ _ _ (1 ⊗ₜ[R] unit.hom.app M)
        (a ⊗ₜ[R] f) = ScalarLocalization.composition R C t _ _ _
          (ScalarLocalization.mapHom R C t H _ _ (a ⊗ₜ[R] f))
          (1 ⊗ₜ[R] unit.hom.app K)
      simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul,
        ScalarLocalization.composition_tmul, one_mul, mul_one]
      exact congrArg (fun g ↦ a ⊗ₜ[R] g) (unit.hom.naturality f)
    | add f g hf hg =>
      change ScalarLocalization.composition R C t K M (H.obj M)
        (1 ⊗ₜ[R] unit.hom.app M) f =
          ScalarLocalization.composition R C t K (H.obj K) (H.obj M)
            (ScalarLocalization.mapHom R C t H K M f)
            (1 ⊗ₜ[R] unit.hom.app K) at hf
      change ScalarLocalization.composition R C t K M (H.obj M)
        (1 ⊗ₜ[R] unit.hom.app M) g =
          ScalarLocalization.composition R C t K (H.obj K) (H.obj M)
            (ScalarLocalization.mapHom R C t H K M g)
            (1 ⊗ₜ[R] unit.hom.app K) at hg
      change ScalarLocalization.composition R C t K M (H.obj M)
        (1 ⊗ₜ[R] unit.hom.app M) (f + g) =
          ScalarLocalization.composition R C t K (H.obj K) (H.obj M)
            (ScalarLocalization.mapHom R C t H K M (f + g))
            (1 ⊗ₜ[R] unit.hom.app K)
      simp only [_root_.map_add, LinearMap.add_apply, hf, hg]
  let unitRat : 𝟭 _ ≅ J := NatIso.ofComponents
    (fun K ↦ Q.mapIso (unit.app K.obj)) (fun {K M} f ↦ hn K M f)
  exact ⟨unitRat, fun _ ↦ rfl⟩

/-- Identification with rational identity compact support through the whole strict
tower, before taking its total limit. The comparison of the two total-limit functors
is normalized on K-injective towers, so an arbitrary isomorphism is not substituted.
The chosen integral compact-support action keeps its original Roos projections.
Source: blueprint opening sentence, strict identity tower
(blueprint: lem-pod-reconstruction-raw-rational-naturality).
Proof (DAG step 3): use the identity compactification (id_s,id_s). Extension by zero
has its original sections on every site object; identity direct image and its derived
resolution comparison give the identity finite-level operation on objects and arrows.
The scalar-restriction comparison is the identity comparison on the same complexes.
The compact-support tower theorem thus identifies its entire strict tower with the
restriction of A.reduction, including quotient transitions and every derived arrow.
Apply the total right-derived limit to this isomorphism. The right-derived universal
property gives the normalized comparison of total-limit models; its projections are
the chosen compact-support Roos projections. Restrict to the full constructible
category, then tensor every integral Hom map and comparison with E. This gives kappaRat
with exactly Q_E(kappa_C), on the raw category with unchanged objects. -/
theorem reconstruction_identityCompactSupport (hl : l ≠ D.p)
    (A : CoefficientDerivedSystemCalculus l E (point D))
    (H : sfIntegralConstructibleCategory l E (point D) ⥤
      sfIntegralConstructibleCategory l E (point D))
    (unit : 𝟭 (sfIntegralConstructibleCategory l E (point D)) ≅ H)
    (hH : IntegralRealization D l E A H unit)
    (J : sfRationalConstructibleCategory l E (point D) ⥤
      sfRationalConstructibleCategory l E (point D))
    (unitRat : 𝟭 (sfRationalConstructibleCategory l E (point D)) ≅ J)
    (hJ : RationalRealization D l E H unit J unitRat) :
    ∃ (hk : IsUnit (l : D.k))
      (T : DerivedCategory (scalarReductionSource l E (point D)) ⥤
        coefficientSequenceRestrictedDerived l E (point D))
      (e : ∀ n : ℕ, T ⋙ coefficientConstantTowerEvaluation l E (point D) n ≅
        compactSupportRestrictedLevel l E (Compactification.ofIsProper (𝟙 (point D))) n)
      (θ : A.reduction ⋙ coefficientSequenceDerivedRestriction l E (point D) ≅ T)
      (ρ : sfCompactSupportFiniteIntegralFunctor l D.k
          hk (Compactification.ofIsProper (𝟙 (point D))) E ⋙
            (sfIntegralConstructible l E (point D)).ι ≅
        (sfIntegralConstructible l E (point D)).ι ⋙ T ⋙
          coefficientConstantTowerLimit l E (point D))
      (η : H ⋙ (sfIntegralConstructible l E (point D)).ι ≅
        (sfIntegralConstructible l E (point D)).ι ⋙ completion.{u, u} D l E A)
      (κ : H ≅ sfCompactSupportFiniteIntegralFunctor l D.k
        hk (Compactification.ofIsProper (𝟙 (point D))) E)
      (κRat : J ≅ sfCompactSupportFiniteFunctor l D.k
        hk (Compactification.ofIsProper (𝟙 (point D))) E),
      T = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E D.k (point D) (point D)
          (𝟙 (point D)) hk
          (Compactification.ofIsProper (𝟙 (point D)))))).2.2 ∧
      (∀ (C : DerivedCategory (scalarReductionSource l E (point D))) (n : ℕ),
        (coefficientConstantTowerEvaluation l E (point D) n).map (θ.hom.app C) ≫
            (e n).hom.app C ≫ (finiteRestrictedIdentity D l E n).hom.app C =
          (coefficientRestrictedEvaluationIso l E (point D) n).hom.app
              (A.reduction.obj C) ≫
            (scalarReductionDerivedRestriction l E (point D) n).map
              ((A.reductionEvaluation n).hom.app C)) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
        (C : DerivedCategory (scalarReductionSource l E (point D))),
        (pbcTowerTransition (point D)
            (completedIntegralCommRingSheafUnrestricted l E (point D)) m n h).app
              (T.obj C) ≫ (e n).hom.app C =
          (e m).hom.app C ≫ compactSupportRestrictedTransition l E
            (Compactification.ofIsProper (𝟙 (point D))) m n h C) ∧
      (∀ C, HEq (η.hom.app C) (𝟙 ((completion.{u, u} D l E A).obj C.obj))) ∧
      isoWhiskerRight κ (sfIntegralConstructible l E (point D)).ι ≪≫ ρ =
        η ≪≫ isoWhiskerLeft (sfIntegralConstructible l E (point D)).ι
          (isoWhiskerRight θ (coefficientConstantTowerLimit l E (point D))) ∧
      (∀ (C : sfIntegralConstructibleCategory l E (point D)) (n : ℕ),
        HEq (ρ.hom.app C ≫
            (coefficientConstantTowerProjection l E (point D) n).app (T.obj C.obj) ≫
              (e n).hom.app C.obj)
          (Classical.choose (Classical.choose_spec
            (exists_isDerivedLimit_and_iso
              (sfCompactSupportTerm l E (Compactification.ofIsProper (𝟙 (point D))) C.obj)
              (sfCompactSupportTransition l E
                (Compactification.ofIsProper (𝟙 (point D))) C.obj)).1) ≫
            Pi.π (sfCompactSupportTerm l E
              (Compactification.ofIsProper (𝟙 (point D))) C.obj) n)) ∧
      ∀ C : sfRationalConstructibleCategory l E (point D),
        HEq (κRat.hom.app C)
          ((sfRationalConstructibleLocalization l E (point D)).map (κ.hom.app C.obj)) := by
  classical
  have hk : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    simpa only [map_natCast] using
      ((CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) hl.symm).isUnit.map
        (algebraMap D.k₀ D.k))
  obtain ⟨T, e, θ, hT, he, hθ, htr⟩ := identityReductionTower D l E hk A
  obtain ⟨ρ, hρ⟩ := compactSupportNormalizedTowerLimit l E D.k hk
    (Compactification.ofIsProper (𝟙 (point D))) T e hT he
  let P := sfIntegralConstructible l E (point D)
  let F := sfCompactSupportFiniteIntegralFunctor l D.k hk
    (Compactification.ofIsProper (𝟙 (point D))) E
  have hη : H ⋙ P.ι = P.ι ⋙ completion D l E A :=
    Functor.hext hH.1 hH.2.1
  let η : H ⋙ P.ι ≅ P.ι ⋙ completion D l E A := eqToIso hη
  let α : H ⋙ P.ι ≅ F ⋙ P.ι :=
    η ≪≫ isoWhiskerLeft P.ι
      (isoWhiskerRight θ (coefficientConstantTowerLimit l E (point D))) ≪≫ ρ.symm
  let κ : H ≅ F := NatIso.ofComponents
    (fun C ↦ P.fullyFaithfulι.preimageIso (α.app C)) (fun {C C'} f ↦ by
      apply P.ι.map_injective
      simpa using α.hom.naturality f)
  have hκ : isoWhiskerRight κ P.ι = α := by
    apply Iso.ext
    apply NatTrans.ext
    funext C
    exact P.fullyFaithfulι.map_preimage _
  have : F.Linear (Padic.coefficientExtensionIntegers l E) :=
    (sfCompactSupportFiniteIntegralFunctor_linear l D.k hk
      (Compactification.ofIsProper (𝟙 (point D))) E).2
  have : F.Additive := Functor.additive_of_iso (unit ≪≫ κ)
  obtain ⟨w, hw⟩ := localizedUnit D l E F (unit ≪≫ κ)
  let κRat : J ≅ sfCompactSupportFiniteFunctor l D.k hk
      (Compactification.ofIsProper (𝟙 (point D))) E := unitRat.symm ≪≫ w
  refine ⟨hk, T, e, θ, ρ, η, κ, κRat, hT, hθ, htr, ?_, ?_, hρ, ?_⟩
  · intro C
    change HEq ((eqToHom hη).app C) _
    rw [eqToHom_app]
    exact eqToHom_heq_id_cod _ _ _
  · rw [hκ]
    simp only [α, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    rfl
  · intro C
    let Q := sfRationalConstructibleLocalization l E (point D)
    have hwin : w.hom.app C = Q.map (unit.hom.app C.obj ≫ κ.hom.app C.obj) := hw C
    change HEq (unitRat.inv.app C ≫ w.hom.app C) (Q.map (κ.hom.app C.obj))
    rw [hwin]
    have hi := (hJ.2.2.2.2.1 C).2
    have hc := comp_heq (hJ.2.2.1 C) rfl rfl hi
      (HEq.rfl : HEq (Q.map (unit.hom.app C.obj ≫ κ.hom.app C.obj))
        (Q.map (unit.hom.app C.obj ≫ κ.hom.app C.obj)))
    apply hc.trans
    apply heq_of_eq
    rw [← Q.map_comp, ← Category.assoc, unit.inv_hom_id_app, Category.id_comp]


end WeilConjectures.PodRawReconstruction
