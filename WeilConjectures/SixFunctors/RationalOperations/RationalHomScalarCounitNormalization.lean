/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
public import WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
import all WeilConjectures.SixFunctors.Normalized.NormalizedRationalEvaluationNaturality
import WeilConjectures.SixFunctors.RationalOperations.OrdinaryCompletedTensorAdjointSquare

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open scoped TensorProduct
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The closed evaluation map associated with a permitted rational Hom pair.
Source: the normalized tensor-Hom counit used in the finite scalar evaluation argument
(blueprint: lem-sf-rational-hom-scalar-evaluation). -/
def normalizedCounit
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K M : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.tensor D l hl X E).obj
        (K, (homRight l E X h K).obj M) ⟶ M :=
  (@pullbackTensorRationalBraiding l _ E _ _ _ X
      (RationalVerdier.units D l hl X) K ((homRight l E X h K).obj M)).hom ≫
    (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
      ⟨(op K, M), h K M⟩

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem normalizedCounit_integral
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K M : sfIntegralConstructibleCategory l E X) :
    HEq (normalizedCounit D l hl X E h
      ((sfRationalConstructibleLocalization l E X).obj K)
      ((sfRationalConstructibleLocalization l E X).obj M))
      ((sfRationalConstructibleLocalization l E X).map
        ((@pullbackTensorIntegralBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) K
          ((constructibleIntegralHom l E X).obj
            (integralPairOfRationalHomPair l E X
              ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                (sfRationalConstructibleLocalization l E X).obj M), h _ _⟩))).hom ≫
          (@podIntegralClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
            (integralPairOfRationalHomPair l E X
              ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                (sfRationalConstructibleLocalization l E X).obj M), h _ _⟩))) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := RationalVerdier.units D l hl X
  let Q := sfRationalConstructibleLocalization l E X
  let P : (constructibleRationalHomPairs l E X).FullSubcategory :=
    ⟨(op (Q.obj K), Q.obj M), h _ _⟩
  let PI := integralPairOfRationalHomPair l E X P
  let H := (rationalDerivedInternalHom l E X).obj P
  let HI := (constructibleIntegralHom l E X).obj PI
  have hH : H = Q.obj HI :=
    (rationalDerivedInternalHom_existsUnique l E X).exists.choose_spec.1 P
  have ht (N V : sfRationalConstructibleCategory l E X) :
      (rationalDerivedTensor l E X).obj (N, V) =
        Q.obj ((constructibleIntegralTensor l E X).obj (N.obj, V.obj)) :=
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 (N, V)
  have hb : HEq (pullbackTensorRationalBraiding l E X (Q.obj K) H).hom
      (Q.map (pullbackTensorIntegralBraiding l E X K HI).hom) := by
    have hh := congrArg ScalarLocalization.obj hH
    have b := (pullbackTensorRationalBraiding_existsUnique l E X
      (Q.obj K) H).exists.choose_spec
    dsimp only [pullbackTensorRationalBraiding]
    have hx (U V : sfIntegralConstructibleCategory l E X) (hh : U = V) :
        HEq (Q.map (pullbackTensorIntegralBraiding l E X K U).hom)
          (Q.map (pullbackTensorIntegralBraiding l E X K V).hom) := by
      cases hh
      rfl
    exact b.trans (hx _ _ hh)
  have he : HEq ((podRationalClosed l E X).evaluation P)
      (Q.map ((podIntegralClosed l E X).evaluation PI)) :=
    rationalEvaluation_normalization l E X P
  have hs : (rationalDerivedTensor l E X).obj (Q.obj K, H) =
      Q.obj ((constructibleIntegralTensor l E X).obj (K, HI)) := by
    rw [hH]
    exact ht _ _
  have hm : (rationalDerivedTensor l E X).obj (H, Q.obj K) =
      Q.obj ((constructibleIntegralTensor l E X).obj (HI, K)) := by
    rw [hH]
    exact ht _ _
  exact (heq_comp hs hm rfl hb he).trans (heq_of_eq (Q.map_comp _ _).symm)

private theorem integralCounit_normalized
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (c : RationalVerdier.Completion D l hl X E a)
    (P : (constructibleIntegralHomPairs l E X).FullSubcategory) :
    (@pullbackTensorIntegralBraiding l _ E _ _ _ X
      (RationalVerdier.units D l hl X) P.obj.1.unop
      ((constructibleIntegralHom l E X).obj P)).hom.hom ≫
        ((@podIntegralClosed l _ E _ _ _ X
          (RationalVerdier.units D l hl X)).evaluation P).hom =
      (@asIso _ _ _ _ (c.map.app
        (P.obj.1.unop.obj, ((constructibleIntegralHom l E X).obj P).obj))
        (c.invertible P.obj.1.unop ((constructibleIntegralHom l E X).obj P))).inv ≫
          (a.adjunction P.obj.1.unop.obj).counit.app P.obj.2.obj := by
  let : ∀ x : X, Invertible (l : X.residueField x) := RationalVerdier.units D l hl X
  let K := P.obj.1.unop
  let H := (constructibleIntegralHom l E X).obj P
  let S := (pullbackTensorCalculus l E X).integralClosed
  have he : podCompletedTensorUnit l E X H.obj K.obj ≫
      ((podIntegralClosed l E X).evaluation P).hom = S.evaluation K.obj P.obj.2.obj := by
    have h := integralInverseTranspose_normalization l E X H P (𝟙 _)
    change _ = ((S.adjunction K.obj).homEquiv _ _).symm (𝟙 _) at h
    have hid : ((S.adjunction K.obj).homEquiv H.obj P.obj.2.obj).symm (𝟙 H.obj) =
        S.evaluation K.obj P.obj.2.obj :=
      (S.adjunction K.obj).homEquiv_symm_id P.obj.2.obj
    exact h.trans hid
  have hc := ordinaryCompletedTensor_adjoint_square D l hl X E a c K H
  have hn := Adjunction.leftAdjointUniq_hom_app_counit
    (a.adjunction K.obj) (S.adjunction K.obj) P.obj.2.obj
  have := c.invertible K H
  apply (cancel_epi (c.map.app (K.obj, H.obj))).1
  change c.map.app (K.obj, H.obj) ≫
      (pullbackTensorIntegralBraiding l E X K H).hom.hom ≫
        ((podIntegralClosed l E X).evaluation P).hom =
    c.map.app (K.obj, H.obj) ≫ inv (c.map.app (K.obj, H.obj)) ≫
      (a.adjunction K.obj).counit.app P.obj.2.obj
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← hc, Category.assoc, he]
  exact hn

/-- The normalized closed counit on an objectwise localized integral pair agrees with
 the localization of the completed ordinary evaluation specified by a HomIdentification.
Source: finite scalar evaluation argument, normalization and localization paragraphs;
 the rational closed evaluation is the scalar localization of the integral closed
 evaluation, and the latter is the inverse completion map followed by ordinary counit.
(blueprint: lem-sf-rational-hom-counit-normalized). -/
theorem normalizedCounit_localized_integral
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w)
    (h : HomIdentification l E X D hl w A)
    (K M : sfIntegralConstructibleCategory l E X) :
    HEq (normalizedCounit D l hl X E h.permitted
      ((sfRationalConstructibleLocalization l E X).obj K)
      ((sfRationalConstructibleLocalization l E X).obj M))
      ((sfRationalConstructibleLocalization l E X).map
        (ObjectProperty.homMk
          (X := (@constructibleIntegralTensor l _ E _ _ _ X
            (RationalVerdier.units D l hl X)).obj
              (K, (constructibleIntegralHom l E X).obj
                (integralPairOfRationalHomPair l E X
                  ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                    (sfRationalConstructibleLocalization l E X).obj M), h.permitted _ _⟩)))
          (Y := M)
          ((@asIso _ _ _ _ (A.completion.map.app
            (K.obj, ((integralDerivedInternalHom l E X).obj (op K.obj, M.obj))))
            (A.completion.invertible K
              ((constructibleIntegralHom l E X).obj
                (integralPairOfRationalHomPair l E X
                  ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                    (sfRationalConstructibleLocalization l E X).obj M), h.permitted _ _⟩)))).inv ≫
            (A.ordinary.adjunction K.obj).counit.app M.obj))) := by
  let P : (constructibleRationalHomPairs l E X).FullSubcategory :=
    ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
      (sfRationalConstructibleLocalization l E X).obj M), h.permitted _ _⟩
  have hi := integralCounit_normalized D l hl X E A.ordinary A.completion
    (integralPairOfRationalHomPair l E X P)
  refine (normalizedCounit_integral D l hl X E h.permitted K M).trans (heq_of_eq ?_)
  apply congrArg (sfRationalConstructibleLocalization l E X).map
  apply ObjectProperty.hom_ext
  exact hi

theorem homIdentification_counit_normalized
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w)
    (h : HomIdentification l E X D hl w A) :
    ∀ K M : sfRationalConstructibleCategory l E X,
      (h.adjunction K).counit.app M = normalizedCounit D l hl X E h.permitted K M := by
  intro K M
  cases K with
  | mk K =>
    cases M with
    | mk M =>
      apply eq_of_heq
      exact (h.integral_evaluation K M).trans
        (normalizedCounit_localized_integral D l hl X E w A h K M).symm

end WeilConjectures.RationalOperations
