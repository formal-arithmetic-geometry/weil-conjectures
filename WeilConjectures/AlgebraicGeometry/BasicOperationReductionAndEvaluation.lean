/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.OperationCoefficientActionData
import WeilConjectures.AlgebraicGeometry.CoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.CompactSupportNormalizedReductionTower
import WeilConjectures.AlgebraicGeometry.NormalizedDVREffectivity
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.FiniteQuotientHomModelComparison
import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
import Mathlib.Data.Nat.Prime.Infinite

/-! # A component of the operation coefficient reduction argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe a b c d t u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

private theorem finiteChangeEvaluation_naturality
    {C : Type a} [Category.{c} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 K')) ≫
      S.evaluation K' M' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M ≫ g := by
  let := S.monoidal
  have hf : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K')) ≫
      S.evaluation K' M =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫ _ =
      S.monoidal.tensorHom (𝟙 (H.obj (op K, M))) f ≫ _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact S.evaluation_naturality K K' M f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K')) ≫
      S.evaluation K' M' = S.evaluation K' M ≫ g := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') ≫ _ = _
    rw [MonoidalCategory.tensorHom_id]
    exact (S.adjunction K').counit.naturality g
  have hh : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 M) ≫ Prod.mkHom (𝟙 (op K')) g := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [hh, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 M)) ≫ H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id]
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private theorem finiteChangeUncurry
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P Q : D) (h : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm h =
      S.tensor.map (Prod.mkHom h (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q h

private theorem finiteChangeTensor_comp
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y Z U V W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) (k : V ⟶ W) :
    S.tensor.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      S.tensor.map (Prod.mkHom f h) ≫ S.tensor.map (Prod.mkHom g k) :=
  S.tensor.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem finiteChangeUncurry_pre
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T U P Q : D}
    (f : T ⟶ U) (h : U ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ h) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose U P Q).symm h := by
  rw [finiteChangeUncurry, finiteChangeUncurry]
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ S.evaluation P Q) (finiteChangeTensor_comp S f h (𝟙 P) (𝟙 P))

private theorem finiteChangeUncurry_post
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T P Q P' Q' : D}
    (h : T ⟶ H.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (S.transpose T P' Q').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm h ≫ g := by
  rw [finiteChangeUncurry_pre, finiteChangeUncurry, finiteChangeEvaluation_naturality]
  rw [finiteChangeUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem finiteChangeBaseChangeHom_beta
    {A : Type*} {B : Type*} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    (SB.transpose _ (F.obj P) (F.obj Q)).symm (coefficientBaseChangeHom SA SB F μ P Q) =
      μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) :=
  Equiv.symm_apply_apply _ _

/-- Evaluation and uniqueness follow directly from the closed adjunction. -/
private theorem finiteHomEvaluation_of_transpose
    {A B : Type a} [Category.{c} A] [Category.{c} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :
    FiniteHomEvaluation SA SB F μ := by
  intro K M
  have hu (v : F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M)) :
      (SB.transpose _ (F.obj K) (F.obj M)).symm v =
        SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
          SB.evaluation (F.obj K) (F.obj M) := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      CoefficientClosedStructure.evaluation] using!
      (SB.adjunction (F.obj K)).homEquiv_counit _ (F.obj M) v
  constructor
  · rw [← hu, coefficientBaseChangeHom, Equiv.symm_apply_apply]
  · intro v hv
    apply (SB.transpose _ (F.obj K) (F.obj M)).symm.injective
    rw [hu, hv, coefficientBaseChangeHom, Equiv.symm_apply_apply]


private theorem finiteChange_natural
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (K K' M M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ K' M' =
      coefficientBaseChangeHom SA SB F μ K M ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply (SB.transpose (F.obj (HA.obj (op K, M))) (F.obj K') (F.obj M')).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeUncurry_post]
  simp only [finiteChangeBaseChangeHom_beta]
  have hμ₁ := μ.inv.naturality
    (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 K'))
  have hμ₂ := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op K, M))) f)
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hμ₁ hμ₂
  rw [← Category.assoc, hμ₁, Category.assoc, ← F.map_comp,
    finiteChangeEvaluation_naturality SA, F.map_comp, F.map_comp, ← Category.assoc,
    ← Category.assoc, ← hμ₂]
  simp only [Category.assoc]

private theorem finiteChange_transpose
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (T K M : A) (f : SA.tensor.obj (T, K) ⟶ M) :
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f) := by
  apply (SB.transpose (F.obj T) (F.obj K) (F.obj M)).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta, Equiv.symm_apply_apply]
  have hn := μ.inv.naturality (Prod.mkHom (SA.transpose T K M f) (𝟙 K))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ← finiteChangeUncurry,
    Equiv.symm_apply_apply]

private theorem finiteChange_composition
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (hAssoc : ∀ X Y Z : A,
      SB.tensor.map (Prod.mkHom (μ.inv.app (X, Y)) (𝟙 (F.obj Z))) ≫
        μ.inv.app (SA.tensor.obj (X, Y), Z) ≫
          F.map (SA.monoidal.associator X Y Z).hom =
      (SB.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫
          μ.inv.app (X, SA.tensor.obj (Y, Z))) (P Q V : A) :
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
          (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V) := by
  let := SA.monoidal
  let := SB.monoidal
  apply (cancel_epi (μ.inv.app (HA.obj (op Q, V), HA.obj (op P, Q)))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (SB.transpose _ (F.obj P) (F.obj V)).symm.injective
  rw [finiteChangeUncurry_pre, finiteChangeUncurry_pre, finiteChangeBaseChangeHom_beta,
    finiteChangeUncurry_pre]
  have hn := μ.inv.naturality (Prod.mkHom (SA.composition P Q V) (𝟙 P))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn
  rw [reassoc_of% hn, ← F.map_comp, ← finiteChangeUncurry]
  simp only [CoefficientClosedStructure.composition, Equiv.symm_apply_apply, F.map_comp]
  rw [reassoc_of% hAssoc]
  have hn' := μ.inv.naturality
    (Prod.mkHom (𝟙 (HA.obj (op Q, V))) (SA.evaluation P Q))
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hn'
  rw [← reassoc_of% hn']
  have hβ (X Y : A) :
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ X Y)
          (𝟙 (F.obj X))) ≫ SB.evaluation (F.obj X) (F.obj Y) =
        μ.inv.app (HA.obj (op X, Y), X) ≫ F.map (SA.evaluation X Y) := by
    rw [← finiteChangeUncurry, finiteChangeBaseChangeHom_beta]
  let v := coefficientBaseChangeHom SA SB F μ
  have hn'' :
      SB.tensor.map (Prod.mkHom (SB.tensor.map (Prod.mkHom (v Q V) (v P Q)))
          (𝟙 (F.obj P))) ≫
        (SB.monoidal.associator (HB.obj (op (F.obj Q), F.obj V))
          (HB.obj (op (F.obj P), F.obj Q)) (F.obj P)).hom =
      (SB.monoidal.associator (F.obj (HA.obj (op Q, V)))
          (F.obj (HA.obj (op P, Q))) (F.obj P)).hom ≫
        SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map] using
      MonoidalCategory.associator_naturality (v Q V) (v P Q) (𝟙 (F.obj P))
  rw [reassoc_of% hn'']
  have hex :
      SB.tensor.map (Prod.mkHom (v Q V)
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))))) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (HB.obj (op (F.obj Q), F.obj V)))
          (SB.evaluation (F.obj P) (F.obj Q))) =
      SB.tensor.map (Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
          (SB.tensor.map (Prod.mkHom (v P Q) (𝟙 (F.obj P))) ≫
            SB.evaluation (F.obj P) (F.obj Q))) ≫
        SB.tensor.map (Prod.mkHom (v Q V) (𝟙 (F.obj Q))) := by
    simp only [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% hex, hβ P Q, hβ Q V]
  have hp : Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V))))
      (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q)) =
      Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (μ.inv.app (HA.obj (op P, Q), P)) ≫
        Prod.mkHom (𝟙 (F.obj (HA.obj (op Q, V)))) (F.map (SA.evaluation P Q)) := by
    ext <;> simp
  rw [hp, SB.tensor.map_comp]
  simp only [Category.assoc]


private theorem operationEvaluationCompatible
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (h : ∀ X Y Z : A,
      μ.hom.app (SA.tensor.obj (X, Y), Z) ≫
          SB.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))) ≫
          (SB.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (SA.monoidal.associator X Y Z).hom ≫
          μ.hom.app (X, SA.tensor.obj (Y, Z)) ≫
          SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z)))) :
    CoefficientEvaluationCompatible SA SB F μ := by
  have hi (X Y Z : A) :
      SB.tensor.map (Prod.mkHom (μ.inv.app (X, Y)) (𝟙 (F.obj Z))) ≫
        μ.inv.app (SA.tensor.obj (X, Y), Z) ≫
          F.map (SA.monoidal.associator X Y Z).hom =
      (SB.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫
          μ.inv.app (X, SA.tensor.obj (Y, Z)) := by
    have : IsIso (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))) :=
      inferInstanceAs (IsIso (((μ.app (X, Y)).prod (Iso.refl (F.obj Z))).hom))
    have : IsIso (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z))) :=
      inferInstanceAs (IsIso (((Iso.refl (F.obj X)).prod (μ.app (Y, Z))).hom))
    apply (cancel_epi (μ.hom.app (SA.tensor.obj (X, Y), Z) ≫
      SB.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))))).1
    apply (cancel_mono (μ.hom.app (X, SA.tensor.obj (Y, Z)) ≫
      SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z))))).1
    have hleft := (SB.tensor.mapIso
      ((μ.app (X, Y)).prod (Iso.refl (F.obj Z)))).hom_inv_id
    have hright := (SB.tensor.mapIso
      ((Iso.refl (F.obj X)).prod (μ.app (Y, Z)))).inv_hom_id
    change SB.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))) ≫
      SB.tensor.map (Prod.mkHom (μ.inv.app (X, Y)) (𝟙 (F.obj Z))) = 𝟙 _ at hleft
    change SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫
      SB.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z))) = 𝟙 _ at hright
    simp only [Category.assoc, reassoc_of% hleft, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app_assoc, hright]
    dsimp only [Functor.comp_obj, Functor.prod_obj, Prod.fst, Prod.snd]
    simpa only [CoefficientClosedStructure.tensor, tensor_obj, Category.comp_id,
      Category.assoc] using (h X Y Z).symm
  exact ⟨fun P Q P' Q' f g ↦ finiteChange_natural SA SB F μ P P' Q Q' f g,
    finiteChange_transpose SA SB F μ, finiteChange_composition SA SB F μ hi⟩

private theorem operationTestDatum (l : ℕ) :
    ∃ D : FiniteFieldDatum.{u}, l ≠ D.p := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨{
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ULift.{u} (ZMod p)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod p)) }, ?_⟩
  change l ≠ p
  omega

private theorem adjacentRoosProjection
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f L p δ) (n : ℕ) :
    p ≫ Pi.π K (n + 1) ≫ f n = p ≫ Pi.π K n := by
  have hz : p ≫ towerTransitionEndomorphism f = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hc
  have hn := congrArg (fun a ↦ a ≫ Pi.π K n) hz
  simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Category.comp_id,
    Preadditive.sub_comp, Category.assoc, towerProductShift, Pi.lift_π,
    zero_comp] at hn
  exact (sub_eq_zero.mp hn).symm

private theorem adjointTransition
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {M : C} {P : A} {Q : B} (a : M ⟶ Rm.obj P) (b : M ⟶ Rn.obj Q)
    (v : P ⟶ S.obj Q) (h : a ≫ Rm.map v ≫ e.hom.app Q = b) :
    (am.homEquiv M P).symm a ≫ v =
      (am.homEquiv M (S.obj (Ln.obj M))).symm
          (an.unit.app M ≫ e.inv.app (Ln.obj M)) ≫
        S.map ((an.homEquiv M Q).symm b) := by
  apply (am.homEquiv M (S.obj Q)).injective
  rw [am.homEquiv_naturality_right, Equiv.apply_symm_apply,
    am.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (cancel_mono (e.hom.app Q)).1
  simp only [Category.assoc]
  have he := e.hom.naturality ((an.homEquiv M Q).symm b)
  dsimp only [Functor.comp_map] at he
  rw [he]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← an.homEquiv_unit, Equiv.apply_symm_apply]
  exact h

open CategoryTheory.Pretriangulated in
private theorem roosTransport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : ℕ → C} [HasProduct X]
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (M : C) (p : M ⟶ ∏ᶜ X) (δ : (∏ᶜ X) ⟶ M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle f M p δ)
    (a : ∀ n, X n ≅ Y n) (q : ∀ n, M ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p ≫ Pi.π X n ≫ (a n).hom = q n) :
    ∃ hprod : HasProduct Y, let := hprod
      ∃ δ' : (∏ᶜ Y) ⟶ M⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g M (Pi.lift q) δ' := by
  let : HasProduct Y :=
    hasProduct_of_equiv_of_iso X Y (Equiv.refl ℕ) (fun n ↦ (a n).symm)
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨inferInstance, A.inv ≫ δ, ?_⟩
  apply isomorphic_distinguished _ hc _
  refine Triangle.isoMk _ _ (Iso.refl M) A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = 𝟙 M ≫ p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_π_assoc,
      Category.id_comp]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (hp n).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 M) = A.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option linter.unusedVariables false in
/-- Integral compact-support reduction, finite quotient evaluation, site-perfect finite
Hom reduction, and integral scalar-extension evaluation: the parts of the operation
reduction argument that the library does not yet state.
Source: blueprint lem-fix-operation-reduction, proof steps 1, 2, 4 and 5;
Stacks 08J9, 0FPT; Bhatt--Scholze 6.7.2 and 6.8.14.

Proof: (1) Compact support. For a compactification `f = p ∘ j`, the integral
compact-support complex is the derived limit `M` of the tower of finite compact-support
images `K_n ↦ p_* j_! K_n`. Its reduction modulo `ϖ^{n+1}` is compared with `p_* j_! K_n`
by the projection `p` and the finite open-extension and proper direct-image coefficient
comparisons; these are isomorphisms because extension by zero is exact, the proper
direct image of a finite-Tor constructible complex commutes with the finite-free
coefficient change, and two derived limits of the same tower are isomorphic compatibly
with their projections. The same projections make the comparisons compatible with the
transition maps, and integral constructibility of `M` follows from that of the
reductions and a uniform cohomological bound (Bhatt--Scholze 6.8.14).
(2) Finite quotient evaluation. On flat-term K-flat representatives the quotient tensor
comparison sends `(x ⊗ a) ⊗ (y ⊗ b)` to `(x ⊗ y) ⊗ ab`; it preserves reassociation on pure
triples and the unit, hence by transposition the internal composition and evaluation
maps; repeated levels `m = n` give identities.
(3) Site-perfect Hom. For site-perfect `P`, ringed-site duality gives
`RHom(P, Q) ≅ P^∨ ⊗ Q` for arbitrary `Q`; the dual of a bounded complex of finite
projectives commutes with the quotient coefficient change termwise, and the
evaluation calculation identifies the result with the evaluation-defined reduction
map, which is therefore an isomorphism, locally and hence globally.
(4) Integral scalar extension `O_E → O_L` is finite free, so the same pure-tensor
calculation as in (2) gives its evaluation compatibility and Hom evaluation laws.
(blueprint: lem-fix-basic-operation-reduction-and-evaluation). -/
theorem basicOperationReductionAndEvaluation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : Scheme.{u}) (f : X ⟶ Y) :
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (K : DerivedCategory (scalarReductionSource l E X))
      (hK : sfIntegralConstructible l E X K)
      (M : DerivedCategory (scalarReductionSource l E Y))
      (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n)
      (δ : (∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) ⟶ M⟦(1 : ℤ)⟧)
      (hδ : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) M p δ),
      sfIntegralConstructible l E Y M ∧
        (∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n)) ∧
        ∀ n : ℕ,
          coefIntegralCompactSupportComparison l E c K M p (n + 1) ≫
              coefCompactSupportFiniteTransition l E c K n =
            sfCompactSupportReductionTransition l E Y M n ≫
              (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory.map
                (coefIntegralCompactSupportComparison l E c K M p n)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n),
      CoefficientEvaluationCompatible (finiteIntrinsicClosed l E W n)
        (finiteIntrinsicClosed l E W m) (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h) ∧
      FiniteHomEvaluation (finiteIntrinsicClosed l E W n) (finiteIntrinsicClosed l E W m)
        (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n)
      (P Q : normalizedDVRDerived l E W n),
      IsProEtaleSitePerfect W (integralCoefficientCommRingSheaf l E W n) P →
      IsIso (finiteIntrinsicReductionHom l E W h P Q)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (W : Scheme.{u}),
      CoefficientEvaluationCompatible (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) ∧
      FiniteHomEvaluation (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W))  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K₀ _ hl₀ _ _ _ _ _ _ _ _ _ _ c K hK M p δ hδ
    obtain ⟨D, hl⟩ := operationTestDatum.{u} l
    obtain ⟨T, a, ht, b₀, b₁, hb, hbounds⟩ :=
      compactSupport_normalizedReductionTower l E K₀ hl₀ c K hK D hl
    let e (n : ℕ) := T.evaluationIso n ≪≫
      (scalarReductionDerivedRestriction l E Y n).mapIso (a n)
    have ht' (n : ℕ) :
        (normalizedDVRTowerTransition l E Y D hl n.le_succ).app T.tower ≫
            (e n).hom = (e (n + 1)).hom ≫ sfCompactSupportTransition l E c K n := ht n
    let : HasProduct (fun n : ℕ ↦
        (normalizedDVRTowerEvaluation l E Y D hl n).obj T.tower) :=
      hasProduct_of_equiv_of_iso (sfCompactSupportTerm l E c K) _
        (Equiv.refl ℕ) e
    obtain ⟨hp, δ', hc'⟩ := roosTransport (sfCompactSupportTransition l E c K)
      (fun n ↦ (normalizedDVRTowerTransition l E Y D hl n.le_succ).app T.tower)
      M p δ hδ (fun n ↦ (e n).symm) (fun n ↦ p ≫ Pi.π _ n ≫ (e n).inv)
      (by
        intro n
        apply (cancel_epi (e (n + 1)).hom).1
        simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id] using congrArg (fun z ↦ z ≫ (e n).inv) (ht' n).symm)
      (fun n ↦ rfl)
    have : HasProduct (sfCompactSupportTerm l E c K) := coefCompactSupportHasProduct l E c K
    let := hp
    obtain ⟨hi, hcoh, hcomplete⟩ := normalizedDVRTower_effectivity l E Y D hl T M
      (Pi.lift (fun n ↦ p ≫ Pi.π _ n ≫ (e n).inv)) δ' hc'
    have heq (n : ℕ) :
        normalizedDVRCounitComparison l E Y D hl T M
            (Pi.lift (fun n ↦ p ≫ Pi.π _ n ≫ (e n).inv)) n ≫ (a n).hom =
          coefIntegralCompactSupportComparison l E c K M p n := by
      dsimp only [normalizedDVRCounitComparison, normalizedDVRIntegralAdjunction,
        coefIntegralCompactSupportComparison]
      rw [← Adjunction.homEquiv_naturality_right_symm]
      congr 1
      dsimp only [e, Iso.trans_inv, Functor.mapIso_inv]
      simp only [Pi.lift_π_assoc, Category.assoc, Iso.inv_hom_id,
        ← CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
        Category.comp_id]
      erw [Category.comp_id]
    have hi' (n : ℕ) : IsIso (coefIntegralCompactSupportComparison l E c K M p n) := by
      rw [← heq n]
      infer_instance
    refine ⟨?_, hi', ?_⟩
    · refine ⟨(sfDerivedComplete_iff_legacy l E Y D hl M).mpr hcomplete,
        b₀, b₁, hb, fun n ↦ ?_⟩
      have : ObjectProperty.IsClosedUnderIsomorphisms
          (intrinsicFiniteTorsionConstructible l E (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n)) Y) :=
        (proEtale_bounded_constructible_isTriangulated Y
          (Padic.coefficientExtensionRing l E (n + 1))).1
      refine ⟨ObjectProperty.prop_of_iso _
        (asIso (coefIntegralCompactSupportComparison l E c K M p n)).symm
        (hbounds n).1, ?_⟩
      intro i hi
      apply (hbounds n).2
      intro hz
      exact hi (hz.of_iso ((@DerivedCategory.homologyFunctor _ _ _
        (HasDerivedCategory.standard _) i).mapIso
          (asIso (coefIntegralCompactSupportComparison l E c K M p n))))
    · intro n
      apply adjointTransition
        (derivedScalarExtensionRestrictionAdjunction l E Y (n + 1)).choose
        (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
        (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory
        (sfCompactSupportDerivedRestrictionComp l E Y n)
      simpa only [sfCompactSupportTransition, coefCompactSupportFiniteTransition,
        Category.assoc] using
        adjacentRoosProjection (sfCompactSupportTransition l E c K) M p δ hδ n
  · intro W m n h
    obtain ⟨D, hl⟩ := operationTestDatum.{u} l
    have ht := (coefficientTensor_normalization l E W D hl).2.2.1 n m h
    exact ⟨operationEvaluationCompatible _ _ _ _ ht,
      finiteHomEvaluation_of_transpose _ _ _ _⟩
  · intro W m n h P Q hP
    let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
    let := integralCoefficientAbSheafify.{u, u} W
    let := integralCoefficientAbLocallyBijective.{u, u} W
    let : ∀ U : W.ProEt, HasSheafify ((ProEt.topology W).over U)
        AddCommGrpCat.{u + 1} := fun U ↦ sitePerfectOverAbSheafify.{u, u} W U
    let : ∀ U : W.ProEt, ((ProEt.topology W).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := fun U ↦ sitePerfectOverAbLocallyBijective.{u, u} W U
    let := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n))
    let := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W m))
    obtain ⟨A, hA, _, _⟩ := sitePerfectScalarHomComparison.{u, u + 2, u} W
      (integralCoefficientCommRingSheaf l E W n)
      (integralCoefficientCommRingSheaf l E W m) (coefficientFiniteQuotient l E W h)
    obtain ⟨e, he⟩ := finiteQuotient_homModel_comparison l E W m n h A
    have : IsIso (siteScalarHomComparison.{u + 1, u, u, u + 2} _
        (coefficientFiniteQuotient l E W h) A P Q) := hA P hP Q
    have : IsIso ((coefficientFiniteInternalHom l E W m).map
        (Prod.mkHom (e.inv.app P).op (e.hom.app Q))) :=
      inferInstanceAs (IsIso ((coefficientFiniteInternalHom l E W m).mapIso
        ((e.app P).symm.op.prod (e.app Q))).hom)
    have hi : IsIso (e.hom.app ((coefficientFiniteInternalHom l E W n).obj (op P, Q)) ≫
        finiteIntrinsicReductionHom l E W h P Q) := by
      rw [← he P Q]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hi
  · intro L _ _ _ ι W
    obtain ⟨D, hl⟩ := operationTestDatum.{u} l
    have ht := (coefficientTensor_normalization l E W D hl).2.2.2.2 L ι
    exact ⟨operationEvaluationCompatible _ _ _ _ ht,
      finiteHomEvaluation_of_transpose _ _ _ _⟩

end WeilConjectures
