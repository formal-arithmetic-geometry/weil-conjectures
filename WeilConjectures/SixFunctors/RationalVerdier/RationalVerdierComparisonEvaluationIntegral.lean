/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorScalarCompletion
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierLocalizedEvaluation
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality
import all WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
import all WeilConjectures.SixFunctors.Coef.CoefIntegralFiniteExtension

/-! # Integral representative evaluation for normalized scalar comparisons

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-comparison-evaluation-integral).

This is the integral representative calculation used by the raw rational evaluation
statement. Its proof is split from the final objectwise transport: uncurry the
internal-Hom transpose, use the completion representative equation on K-flat
models, and localize the resulting evaluation square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures

attribute [local irreducible] rationalDerivedTensor integralCompletedTensor
  integralCompletedTensorComparison
  integralOperationsTensorComplexFunctor IntegralHom.totalTensor IntegralHom.homModelMap
  IntegralHom.projection IntegralHom.evaluate
attribute [local implicit_reducible] constructibleIntegralTensor
  IntegralVerdier.restrictedDual IntegralVerdier.dual

namespace RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem map_heq {C : Type*} [Category* C] {C' : Type*} [Category* C']
    (F : C ⥤ C') {K M K' M' : C} (hK : K = K') (hM : M = M')
    {f : K ⟶ M} {g : K' ⟶ M'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hK; cases hM; cases h
  rfl

private theorem id_heq {C : Type*} [Category* C] {K M : C} (h : K = M) :
    HEq (𝟙 K) (𝟙 M) := by cases h; rfl

private theorem tensor_map_heq {C : Type*} [Category* C] (B : C × C ⥤ C)
    {X X' Y Y' M M' N N' : C}
    (hx : X = X') (hy : Y = Y') (hm : M = M') (hn : N = N')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : M ⟶ N} {g' : M' ⟶ N'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (B.map (Prod.mkHom f g)) (B.map (Prod.mkHom f' g')) := by
  cases hx; cases hy; cases hm; cases hn; cases hf; cases hg
  rfl

private theorem iso_inv_heq {C : Type*} [Category* C] {X Y X' Y' : C}
    (e : X ≅ Y) (e' : X' ≅ Y') (hx : X = X') (hy : Y = Y')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hx; cases hy
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem rationalTensor_integral
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K K' M M' : sfIntegralConstructibleCategory l E X) (f : K ⟶ K') (g : M ⟶ M') :
    HEq ((tensor D l hl X E).map (Prod.mkHom
      ((sfRationalConstructibleLocalization l E X).map f)
      ((sfRationalConstructibleLocalization l E X).map g)))
      ((sfRationalConstructibleLocalization l E X).map
        ((integralTensor D l hl X E).map (Prod.mkHom f g))) := by
  obtain ⟨b, hb, hgen⟩ :=
    (@rationalTensor_spec l _ E _ _ _ X (units D l hl X)).2
      ((sfRationalConstructibleLocalization l E X).obj K)
      ((sfRationalConstructibleLocalization l E X).obj K')
      ((sfRationalConstructibleLocalization l E X).obj M)
      ((sfRationalConstructibleLocalization l E X).obj M')
  have hm : (tensor D l hl X E).map (Prod.mkHom
      ((sfRationalConstructibleLocalization l E X).map f)
      ((sfRationalConstructibleLocalization l E X).map g)) = _ := hb _ _
  have h := hgen f g 1 1
  simp only [one_mul] at h
  exact (heq_of_eq hm).trans h

private theorem inverse_square {C : Type*} [Category* C] {U V U' V' : C}
    (a : U ≅ U') (b : V ≅ V') (f : U ⟶ V) (g : U' ⟶ V')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).1
  calc
    a.hom ≫ g ≫ b.inv = (f ≫ b.hom) ≫ b.inv := by rw [h, Category.assoc]
    _ = f := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = a.hom ≫ a.inv ≫ f := by rw [Iso.hom_inv_id_assoc]

private theorem paste_four {C : Type*} [Category* C]
    {A B C' D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D) (d : D ⟶ E)
    (e : E ⟶ F) (f : F ⟶ G) (r : A ⟶ H) (s : H ⟶ E)
    (h : a ≫ b ≫ c ≫ d = r ≫ s) :
    a ≫ (b ≫ c ≫ d ≫ e) ≫ f = r ≫ (s ≫ e) ≫ f := by
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ e ≫ f) h

private abbrev evalI
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : Datum D l hl X E w) (K : sfIntegralConstructibleCategory l E X) :=
  integralEvaluation D l hl X E w.omega A.preserves A.ordinary A.completion K

private theorem completed_beta_evaluation
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (K : sfIntegralConstructibleCategory l E X) :
    let T := integralScalar l X E L i
    let DE := IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves
    let DL := IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves
    let beta : T.obj (DE.obj (op K)) ⟶ DL.obj (op (T.obj K)) :=
      ObjectProperty.homMk
        (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
          K.obj K.property.1)
    (integralTensor D l hl X L).map (Prod.mkHom (𝟙 (T.obj K)) beta) ≫
        evalI D l hl X L wL B (T.obj K) =
      (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X
        (units D l hl X) K (DE.obj (op K))).inv ≫
        T.map (evalI D l hl X E wE A K) ≫
          ObjectProperty.homMk (X := T.obj wE.omega) (Y := wL.omega)
            (IntegralFiniteExtension.u l E L i X D hl wE wL) := by
  dsimp only
  apply ObjectProperty.hom_ext
  let T := integralScalarExtensionOfUniverses l E L i X
  let F := pbcDerivedExtend (completedCoefficientMap l E L i X)
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let DK := (IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)
  let TK := (integralScalar l X E L i).obj K
  let TDK := (integralScalar l X E L i).obj DK
  let DTK := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj (op TK)
  let beta := IntegralFiniteExtension.beta l E L i X D hl wE wL
    A.ordinary B.ordinary K.obj K.property.1
  let c (P Q : sfIntegralConstructibleCategory l L X) :=
    @asIso _ _ _ _ (B.completion.map.app (P.obj, Q.obj)) (B.completion.invertible P Q)
  have hc := B.completion.map.naturality (Prod.mkHom (𝟙 TK.obj) beta)
  change B.ordinary.tensor.map (Prod.mkHom (𝟙 TK.obj) beta) ≫ (c TK DTK).hom =
    (c TK TDK).hom ≫ (integralCompletedTensor l L X).map
      (Prod.mkHom (𝟙 TK.obj) beta) at hc
  have hci : (integralCompletedTensor l L X).map
      (Prod.mkHom (𝟙 TK.obj) beta) ≫ (c TK DTK).inv =
    (c TK TDK).inv ≫ B.ordinary.tensor.map (Prod.mkHom (𝟙 TK.obj) beta) := by
    exact inverse_square (c TK TDK) (c TK DTK) _ _ hc
  have heval : B.ordinary.tensor.map (Prod.mkHom (𝟙 TK.obj) beta) ≫
      (B.ordinary.adjunction TK.obj).counit.app wL.omega.obj =
    IntegralFiniteExtension.extendedEvaluation l E L i X A.ordinary B.ordinary
      K.obj wE.omega.obj K.property.1 wE.omega.property.1 ≫
        IntegralFiniteExtension.u l E L i X D hl wE wL := by
    unfold beta IntegralFiniteExtension.beta
    have ht : B.ordinary.tensor.map (Prod.mkHom (𝟙 TK.obj)
        (IntegralFiniteExtension.v l E L i X A.ordinary B.ordinary K.obj
          wE.omega.obj K.property.1 wE.omega.property.1 ≫
            H.map (Prod.mkHom (𝟙 _) (IntegralFiniteExtension.u l E L i X D hl wE wL)))) =
      B.ordinary.tensor.map (Prod.mkHom (𝟙 TK.obj)
        (IntegralFiniteExtension.v l E L i X A.ordinary B.ordinary K.obj
          wE.omega.obj K.property.1 wE.omega.property.1)) ≫
        B.ordinary.tensor.map (Prod.mkHom (𝟙 TK.obj)
          (H.map (Prod.mkHom (𝟙 _) (IntegralFiniteExtension.u l E L i X D hl wE wL)))) := by
      rw [← B.ordinary.tensor.map_comp]
      simp only [prod_comp, Category.id_comp]
    dsimp only [H] at ht
    erw [ht, Category.assoc]
    have hn := (B.ordinary.adjunction TK.obj).counit.naturality
      (IntegralFiniteExtension.u l E L i X D hl wE wL)
    simp only [Functor.comp_map, Functor.curry_obj_obj_map, Functor.id_map] at hn
    erw [hn, ← Category.assoc,
      IntegralFiniteExtension.v_evaluation l E L i X A.ordinary B.ordinary
        (IntegralHom.evaluation_naturality X _ B.ordinary)
        K.obj wE.omega.obj K.property.1 wE.omega.property.1]
    rfl
  change (integralCompletedTensor l L X).map (Prod.mkHom (𝟙 TK.obj) beta) ≫
      (c TK DTK).inv ≫ (B.ordinary.adjunction TK.obj).counit.app wL.omega.obj =
    (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X
      (units D l hl X) K DK).inv.hom ≫
      T.map ((@asIso _ _ _ _ (A.completion.map.app (K.obj, DK.obj))
        (A.completion.invertible K DK)).inv ≫
          (A.ordinary.adjunction K.obj).counit.app wE.omega.obj) ≫
            IntegralFiniteExtension.u l E L i X D hl wE wL
  erw [← Category.assoc, hci, Category.assoc, heval]
  have hnat := (completedScalarComparison l E L i X).naturality
    ((A.ordinary.adjunction K.obj).counit.app wE.omega.obj)
  change F.map _ ≫ (IntegralFiniteExtension.completion l E L i X
      wE.omega.obj wE.omega.property.1).hom =
    (completedScalarComparison l E L i X).app (A.ordinary.tensor.obj (K.obj, DK.obj)) ≫
      T.map ((A.ordinary.adjunction K.obj).counit.app wE.omega.obj) at hnat
  unfold IntegralFiniteExtension.extendedEvaluation
  erw [hnat]
  have hs := tensor_scalar_completion D l hl X E L i A.ordinary B.ordinary
    A.completion B.completion K DK
  change (c TK TDK).inv ≫ _ ≫ _ ≫ _ = _ at hs
  erw [Functor.map_comp]
  exact paste_four _ _ _ _ _ _ _ _ hs

/-- Integral-representative evaluation compatibility.
Source: blueprint thm-coef-rational-verdier.proof.md, paragraph 3; the
internal-Hom transpose and completion representative calculation.
(blueprint: lem-coef-rational-verdier-comparison-evaluation-integral).

Proof: uncurry the internal-Hom comparison on a K-flat integral representative.
The inverse tensor-Hom adjunction turns `homMap` into scalar-extended ordinary
evaluation; postcomposition with `u` is `beta`. The completion representative
identity identifies this with the prescribed completed tensorator on pure
homogeneous tensors and hence on the localized object. Apply the two HEq
normalizations `hu` and `hb` to retain the displayed endpoint transports. -/
theorem normalizedExtension_evaluation_integral
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (e : Extension D l hl X E L i wE wL A B)
    (hu : (HEq e.omega.hom ((sfRationalConstructibleLocalization l L X).map
    (ObjectProperty.homMk (X := (integralScalar l X E L i).obj wE.omega) (Y := wL.omega)
      (IntegralFiniteExtension.u l E L i X D hl wE wL)))))
    (hb : (∀ K : sfIntegralConstructibleCategory l E X,
    HEq (e.comparison.hom.app (op ((sfRationalConstructibleLocalization l E X).obj K)))
      ((sfRationalConstructibleLocalization l L X).map
        (ObjectProperty.homMk
          (X := (integralScalar l X E L i).obj
            ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
          (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
            (op ((integralScalar l X E L i).obj K)))
          (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
            K.obj K.property.1))))) :
    ∀ K : sfIntegralConstructibleCategory l E X, HEq
      ((tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((scalar l X E L i).obj
          ((sfRationalConstructibleLocalization l E X).obj K)))
          (e.comparison.hom.app (op ((sfRationalConstructibleLocalization l E X).obj K)))) ≫
        B.evaluation ((scalar l X E L i).obj
          ((sfRationalConstructibleLocalization l E X).obj K)))
      ((@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)).inv.app
        ((sfRationalConstructibleLocalization l E X).obj K,
          A.dual.obj (op ((sfRationalConstructibleLocalization l E X).obj K))) ≫
        (scalar l X E L i).map (A.evaluation
          ((sfRationalConstructibleLocalization l E X).obj K)) ≫ e.omega.hom) := by
  let J := sfRationalConstructibleLocalization l E X
  let Q := sfRationalConstructibleLocalization l L X
  let T := integralScalar l X E L i
  let F := scalar l X E L i
  let DE := IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves
  let DL := IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves
  let TE := integralTensor D l hl X E
  let TL := integralTensor D l hl X L
  let RE := tensor D l hl X E
  let RL := tensor D l hl X L
  let mu := @rationalTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)
  have hF (P : sfRationalConstructibleCategory l E X) : F.obj P = Q.obj (T.obj P.obj) :=
    sfRationalScalarExtension_obj l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i P
  have hRE (P N : sfRationalConstructibleCategory l E X) :
      RE.obj (P, N) = J.obj (TE.obj (P.obj, N.obj)) :=
    (@rationalTensor_spec l _ E _ _ _ X (units D l hl X)).1
      (P, N)
  have hRL (P N : sfRationalConstructibleCategory l L X) :
      RL.obj (P, N) = Q.obj (TL.obj (P.obj, N.obj)) :=
    (@rationalTensor_spec l _ L _ _ _ X (units D l hl X)).1
      (P, N)
  intro K
  let DK := DE.obj (op K)
  let TK := T.obj K
  let TDK := T.obj DK
  let DTK := DL.obj (op TK)
  let beta : TDK ⟶ DTK := ObjectProperty.homMk
    (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
      K.obj K.property.1)
  let m := @integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X) K DK
  have hDK : A.dual.obj (op (J.obj K)) = J.obj DK := A.objects (J.obj K)
  have hFDK : F.obj (A.dual.obj (op (J.obj K))) = Q.obj TDK := by
    rw [hDK, hF]
    rfl
  have hDTK : B.dual.obj (op (F.obj (J.obj K))) = Q.obj DTK := by
    rw [hF]
    exact B.objects _
  have hdom : RL.obj (F.obj (J.obj K), F.obj (A.dual.obj (op (J.obj K)))) =
      Q.obj (TL.obj (TK, TDK)) := by
    rw [hF, hFDK, hRL]
    rfl
  have hmid : RL.obj (F.obj (J.obj K), B.dual.obj (op (F.obj (J.obj K)))) =
      Q.obj (TL.obj (TK, DTK)) := by
    rw [hDTK, hF, hRL]
    rfl
  have hE : RE.obj (J.obj K, A.dual.obj (op (J.obj K))) = J.obj (TE.obj (K, DK)) := by
    rw [hDK, hRE]
    rfl
  have hscalar : F.obj (RE.obj (J.obj K, A.dual.obj (op (J.obj K)))) =
      Q.obj (T.obj (TE.obj (K, DK))) := by
    rw [hE, hF]
    rfl
  have hmap : HEq (RL.map (Prod.mkHom (𝟙 (F.obj (J.obj K)))
      (e.comparison.hom.app (op (J.obj K)))))
      (Q.map (TL.map (Prod.mkHom (𝟙 TK) beta))) := by
    have ht := tensor_map_heq RL (hF (J.obj K)) (hF (J.obj K)) hFDK hDTK
      (id_heq (hF (J.obj K))) (hb K)
    have hi := rationalTensor_integral D l hl X L TK TK TDK DTK (𝟙 TK) beta
    rw [Q.map_id] at hi
    exact ht.trans hi
  have hevB : HEq (B.evaluation (F.obj (J.obj K)))
      (Q.map (evalI D l hl X L wL B TK)) :=
    (congr_arg_heq B.evaluation (hF (J.obj K))).trans (B.evaluation_integral TK)
  have hleft := heq_comp hdom hmid rfl hmap hevB
  have hmuHom : HEq (mu.hom.app (J.obj K, A.dual.obj (op (J.obj K)))) (Q.map m.hom) := by
    have h := (@rationalTensorScalarComparison_existsUnique l _ E _ _ _ L _ _ _ i X
      (units D l hl X)).exists.choose_spec (J.obj K) (A.dual.obj (op (J.obj K)))
    have hi : (A.dual.obj (op (J.obj K))).obj = DK := congrArg ScalarLocalization.obj hDK
    change HEq (mu.hom.app _) (Q.map
      (@integralTensorScalarComparison l _ E _ _ _ L _ _ _ i X (units D l hl X)
        (J.obj K).obj (A.dual.obj (op (J.obj K))).obj).hom) at h
    rw [hi] at h
    exact h
  have hmu : HEq (mu.inv.app (J.obj K, A.dual.obj (op (J.obj K)))) (Q.map m.inv) :=
    iso_inv_heq (mu.app (J.obj K, A.dual.obj (op (J.obj K)))) (Q.mapIso m)
      hscalar hdom hmuHom
  have hevA : HEq (F.map (A.evaluation (J.obj K)))
      (Q.map (T.map (evalI D l hl X E wE A K))) := by
    have h := map_heq F hE rfl (A.evaluation_integral K)
    have ht := sfRationalScalarExtension_map_tmul l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i _ _ (evalI D l hl X E wE A K) 1
    simp only [map_one] at ht
    exact h.trans ht
  have hr := heq_comp hscalar (hF (J.obj wE.omega)) rfl hevA hu
  have hright := heq_comp hdom hscalar rfl hmu hr
  have hi := congrArg Q.map (completed_beta_evaluation D l hl X E L i wE wL A B K)
  simp only [Functor.map_comp] at hi
  exact hleft.trans ((heq_of_eq hi).trans hright.symm)

end RationalVerdier

end WeilConjectures
