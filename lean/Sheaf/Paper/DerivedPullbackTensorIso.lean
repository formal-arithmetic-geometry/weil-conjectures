/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.NormalizedCompletedOperationModels
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso).

## Main definitions

* The four `canonical*PullbackTensor` families are the prescribed comparisons.
* The higher coherence predicates state equations on those same comparisons.

## Main statements

* `derivedPullbackTensorIso` packages naturality and the higher compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

private theorem coefficientPrime_isUnit (l : ℕ) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply RingedSpace.isUnit_of_isUnit_germ W.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : W.residueField x)).ne_zero

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

private theorem existsUnique_iso_of_eq {C : Type*} [Category* C]
    {A B A' B' : C} (hA : A = A') (hB : B = B') (e : A' ≅ B') :
    ∃! d : A ≅ B, HEq d.hom e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    subst A'
    subst B'
    exact ⟨e, HEq.rfl, fun d hd ↦ Iso.ext (eq_of_heq hd)⟩

private theorem existsUnique_iso_of_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} (e : F.obj A ≅ F.obj B) :
    ∃! d : A ≅ B, F.map d.hom = e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    refine ⟨F.preimageIso e, F.map_preimage _, ?_⟩
    intro d hd
    exact Iso.ext (F.map_injective (hd.trans (F.map_preimage e.hom).symm))

private theorem existsUnique_iso_of_map_comp {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} {T : D}
    (a : F.obj A ≅ T) (b : F.obj B ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b.hom = a.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map F (a ≪≫ b.symm)
    refine ⟨d, ?_, ?_⟩
    · change F.map d.hom ≫ b.hom = a.hom
      rw [hd]
      simp
    · intro e he
      apply hu
      exact (Iso.eq_comp_inv b).mpr he

private theorem existsUnique_iso_of_map_constraints {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B : C} {U V W T : D}
    (a₁ : F.obj A ≅ U) (a₂ : U ≅ V) (a₃ : V ≅ T)
    (b₁ : F.obj B ≅ W) (b₂ : W ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b₁.hom ≫ b₂.hom =
      a₁.hom ≫ a₂.hom ≫ a₃.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [Iso.trans_hom, Category.assoc] using
      existsUnique_iso_of_map_comp F (a₁ ≪≫ a₂ ≪≫ a₃) (b₁ ≪≫ b₂)

private theorem existsUnique_iso_of_map_constraint {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B : C} {U T : D} (a₁ : F.obj A ≅ U) (a₂ : U ≅ T) (b : F.obj B ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b.hom = a₁.hom ≫ a₂.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact existsUnique_iso_of_map_comp F (a₁ ≪≫ a₂) b

private def closedTensorUnitIso {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S T : CoefficientClosedStructure H) :
    S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit :=
  (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    ((T.adjunction T.monoidal.tensorUnit).leftAdjointUniq
      (S.adjunction T.monoidal.tensorUnit)).app S.monoidal.tensorUnit ≪≫
    S.monoidal.leftUnitor T.monoidal.tensorUnit


private theorem map_localized_heq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (F : C ⥤ D) (F' : C' ⥤ D') (Q : C ⥤ C') (R : D ⥤ D')
    (hF : ∀ {A B : C} (f : A ⟶ B), HEq (F'.map (Q.map f)) (R.map (F.map f)))
    {A B : C'} {A' B' : C} (hA : A = Q.obj A') (hB : B = Q.obj B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f (Q.map g)) :
    HEq (F'.map f) (R.map (F.map g)) := by
  subst A B
  cases hfg
  exact hF g

section ReductionCalculus
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem reduction_comparison
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (L : S ⥤ C) (A : R ⊣ L)
    (Q : D ⥤ T) (K : T ⥤ D) (B : Q ⊣ K)
    (F : D ⥤ C) (H : T ⥤ S) (U : D × D ⥤ D) (V : C × C ⥤ C)
    (J : T × T ⥤ T) (I : S × S ⥤ S)
    (a : F ≅ Q ⋙ H ⋙ L) (b : U ≅ (Q.prod Q) ⋙ J ⋙ K)
    (c : V ≅ (R.prod R) ⋙ I ⋙ L)
    (μ : J ⋙ H ≅ (H.prod H) ⋙ I) (M N : D)
    [IsIso (B.counit.app (J.obj (Q.obj M, Q.obj N)))]
    [IsIso (A.counit.app (H.obj (Q.obj M)))]
    [IsIso (A.counit.app (H.obj (Q.obj N)))] :
    R.map (a.hom.app (U.obj (M, N)) ≫
      L.map (H.map (Q.map (b.hom.app (M, N)))) ≫
      L.map (H.map (B.counit.app (J.obj (Q.obj M, Q.obj N)))) ≫
      L.map (μ.hom.app (Q.obj M, Q.obj N)) ≫
      L.map (I.map (Prod.mkHom (inv (A.counit.app (H.obj (Q.obj M))))
        (inv (A.counit.app (H.obj (Q.obj N)))))) ≫
      L.map (I.map (Prod.mkHom (R.map (a.inv.app M)) (R.map (a.inv.app N)))) ≫
      c.inv.app (F.obj M, F.obj N)) ≫
      R.map (c.hom.app (F.obj M, F.obj N)) ≫
      A.counit.app (I.obj (R.obj (F.obj M), R.obj (F.obj N))) ≫
      I.map (Prod.mkHom (R.map (a.hom.app M) ≫ A.counit.app (H.obj (Q.obj M)))
        (R.map (a.hom.app N) ≫ A.counit.app (H.obj (Q.obj N)))) =
    R.map (a.hom.app (U.obj (M, N))) ≫
      A.counit.app (H.obj (Q.obj (U.obj (M, N)))) ≫
      H.map (Q.map (b.hom.app (M, N))) ≫
      H.map (B.counit.app (J.obj (Q.obj M, Q.obj N))) ≫
      μ.hom.app (Q.obj M, Q.obj N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (c.inv.app _) (c.hom.app _), c.inv_hom_id_app, R.map_id, Category.id_comp]
  simp only [A.counit_naturality_assoc]
  simp only [← I.map_comp, CategoryTheory.prod_comp, ← R.map_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  erw [R.map_id, R.map_id]
  simp only [Category.id_comp, IsIso.inv_hom_id]
  erw [← prod_id, I.map_id, Category.comp_id]

private theorem counit_model_naturality
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (R : D ⥤ T) (L : T ⥤ D) (adj : R ⊣ L) (F : C ⥤ D) (H : C ⥤ T)
    (a : F ≅ H ⋙ L) {M N : C} (f : M ⟶ N) :
    R.map (F.map f) ≫ R.map (a.hom.app N) ≫ adj.counit.app (H.obj N) =
      R.map (a.hom.app M) ≫ adj.counit.app (H.obj M) ≫ H.map f := by
  rw [← R.map_comp_assoc, a.hom.naturality, R.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  exact congrArg (fun k ↦ R.map (a.hom.app M) ≫ k)
    (adj.counit.naturality (H.map f))

private theorem reduced_braiding
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : ∀ M N, R.obj (U.obj (M, N)) ≅ J.obj (R.obj M, R.obj N))
    (b : ∀ M N, Q.obj (V.obj (M, N)) ≅ I.obj (Q.obj M, Q.obj N))
    (p : F ⋙ Q ≅ R ⋙ H)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (ν : ∀ M N, H.obj (J.obj (M, N)) ≅ I.obj (H.obj M, H.obj N))
    (βC : ∀ M N, U.obj (M, N) ≅ U.obj (N, M))
    (βD : ∀ M N, V.obj (M, N) ≅ V.obj (N, M))
    (βS : ∀ M N, J.obj (M, N) ≅ J.obj (N, M))
    (βT : I ≅ pullbackTensorSwap T ⋙ I)
    (hC : ∀ M N, R.map (βC M N).hom ≫ (a N M).hom =
      (a M N).hom ≫ (βS (R.obj M) (R.obj N)).hom)
    (hD : ∀ M N, Q.map (βD M N).hom ≫ (b N M).hom =
      (b M N).hom ≫ βT.hom.app (Q.obj M, Q.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ (b (F.obj M) (F.obj N)).hom ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a M N).hom ≫ (ν (R.obj M) (R.obj N)).hom)
    (hν : ∀ M N, H.map (βS M N).hom ≫ (ν N M).hom =
      (ν M N).hom ≫ βT.hom.app (H.obj M, H.obj N)) (M N : C) :
    F.map (βC M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (βD (F.obj M) (F.obj N)).hom := by
  apply Q.map_injective
  let d := b (F.obj N) (F.obj M) ≪≫ I.mapIso (Iso.prod (p.app N) (p.app M))
  apply (cancel_mono d.hom).1
  change _ ≫ ((b (F.obj N) (F.obj M)).hom ≫
    I.map (Prod.mkHom (p.hom.app N) (p.hom.app M))) =
    _ ≫ ((b (F.obj N) (F.obj M)).hom ≫
    I.map (Prod.mkHom (p.hom.app N) (p.hom.app M)))
  simp only [Functor.map_comp, Category.assoc]
  rw [hμ]
  have hp := p.hom.naturality (βC M N).hom
  change Q.map (F.map _) ≫ p.hom.app _ = p.hom.app _ ≫ H.map (R.map _) at hp
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hC, H.map_comp]
  simp only [Category.assoc]
  rw [hν]
  rw [← Category.assoc (Q.map (βD (F.obj M) (F.obj N)).hom), hD]
  simp only [Category.assoc]
  have hn := βT.hom.naturality (Prod.mkHom (p.hom.app M) (p.hom.app N))
  change I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) ≫ _ =
    _ ≫ I.map (Prod.mkHom (p.hom.app N) (p.hom.app M)) at hn
  dsimp only [Functor.comp_obj] at hn
  erw [← hn]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ βT.hom.app (H.obj (R.obj M), H.obj (R.obj N))) (hμ M N).symm

private theorem map_pair_comp
    {C D S : Type*} [Category* C] [Category* D] [Category* S]
    (I : C × D ⥤ S) {A B C' : C} {X Y Z : D}
    (f : A ⟶ B) (g : X ⟶ Y) (f' : B ⟶ C') (g' : Y ⟶ Z) :
    I.map (Prod.mkHom f g) ≫ I.map (Prod.mkHom f' g') =
      I.map (Prod.mkHom (f ≫ f') (g ≫ g')) := by
  rw [← I.map_comp]
  rfl

private theorem nested_right
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        ν.hom.app (R.obj M, R.obj N)) (M N P : C) :
    Q.map (μ M (U.obj (N, P))).hom ≫
      Q.map (V.map (Prod.mkHom (𝟙 _) (μ N P).hom)) ≫
      b.hom.app (F.obj M, V.obj (F.obj N, F.obj P)) ≫
      I.map (Prod.mkHom (p.hom.app M)
        (b.hom.app (F.obj N, F.obj P) ≫
          I.map (Prod.mkHom (p.hom.app N) (p.hom.app P)))) =
    p.hom.app (U.obj (M, U.obj (N, P))) ≫
      H.map (a.hom.app (M, U.obj (N, P))) ≫
      H.map (J.map (Prod.mkHom (𝟙 _) (a.hom.app (N, P)))) ≫
      ν.hom.app (R.obj M, J.obj (R.obj N, R.obj P)) ≫
      I.map (Prod.mkHom (𝟙 _) (ν.hom.app (R.obj N, R.obj P))) := by
  have hb := b.hom.naturality (Prod.mkHom (𝟙 (F.obj M)) (μ N P).hom)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hb
  rw [← Category.assoc (Q.map (V.map _)), hb]
  simp only [Category.assoc]
  rw [map_pair_comp]
  erw [Q.map_id, Category.id_comp]
  rw [hμ]
  have hs := map_pair_comp I (p.hom.app M) (p.hom.app (U.obj (N, P)))
    (𝟙 _) (H.map (a.hom.app (N, P)) ≫ ν.hom.app (R.obj N, R.obj P))
  simp only [Category.comp_id] at hs
  rw [← hs]
  rw [reassoc_of% hμ]
  have hs' := map_pair_comp I (𝟙 (H.obj (R.obj M))) (H.map (a.hom.app (N, P)))
    (𝟙 _) (ν.hom.app (R.obj N, R.obj P))
  simp only [Category.id_comp] at hs'
  erw [← hs']
  have hn := ν.hom.naturality
    (Prod.mkHom (𝟙 (R.obj M)) (a.hom.app (N, P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [H.map_id] at hn
  erw [← reassoc_of% hn]
  rfl

private theorem nested_left
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        ν.hom.app (R.obj M, R.obj N)) (M N P : C) :
    Q.map (μ (U.obj (M, N)) P).hom ≫
      Q.map (V.map (Prod.mkHom (μ M N).hom (𝟙 _))) ≫
      b.hom.app (V.obj (F.obj M, F.obj N), F.obj P) ≫
      I.map (Prod.mkHom
        (b.hom.app (F.obj M, F.obj N) ≫
          I.map (Prod.mkHom (p.hom.app M) (p.hom.app N))) (p.hom.app P)) =
    p.hom.app (U.obj (U.obj (M, N), P)) ≫
      H.map (a.hom.app (U.obj (M, N), P)) ≫
      H.map (J.map (Prod.mkHom (a.hom.app (M, N)) (𝟙 _))) ≫
      ν.hom.app (J.obj (R.obj M, R.obj N), R.obj P) ≫
      I.map (Prod.mkHom (ν.hom.app (R.obj M, R.obj N)) (𝟙 _)) := by
  have hb := b.hom.naturality (Prod.mkHom (μ M N).hom (𝟙 (F.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hb
  rw [← Category.assoc (Q.map (V.map _)), hb]
  simp only [Category.assoc]
  rw [map_pair_comp]
  erw [Q.map_id, Category.id_comp]
  rw [hμ]
  have hs := map_pair_comp I (p.hom.app (U.obj (M, N))) (p.hom.app P)
    (H.map (a.hom.app (M, N)) ≫ ν.hom.app (R.obj M, R.obj N)) (𝟙 _)
  simp only [Category.comp_id] at hs
  rw [← hs]
  rw [reassoc_of% hμ]
  have hs' := map_pair_comp I (H.map (a.hom.app (M, N))) (𝟙 (H.obj (R.obj P)))
    (ν.hom.app (R.obj M, R.obj N)) (𝟙 _)
  simp only [Category.id_comp] at hs'
  erw [← hs']
  have hn := ν.hom.naturality
    (Prod.mkHom (a.hom.app (M, N)) (𝟙 (R.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [H.map_id] at hn
  erw [← reassoc_of% hn]
  rfl

private theorem transport_associator
    {C T : Type*} [Category* C] [Category* T]
    (Q : C ⥤ T) (V : C × C ⥤ C) (I : T × T ⥤ T)
    (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (αC : ∀ M N P, V.obj (V.obj (M, N), P) ≅ V.obj (M, V.obj (N, P)))
    (αT : ∀ M N P, I.obj (I.obj (M, N), P) ≅ I.obj (M, I.obj (N, P)))
    (hn : ∀ {M N P M' N' P' : T} (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P'),
      I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h) ≫ (αT M' N' P').hom =
        (αT M N P).hom ≫ I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
    (hc : ∀ M N P, Q.map (αC M N P).hom ≫ b.hom.app (M, V.obj (N, P)) ≫
      I.map (Prod.mkHom (𝟙 _) (b.hom.app (N, P))) =
        b.hom.app (V.obj (M, N), P) ≫
          I.map (Prod.mkHom (b.hom.app (M, N)) (𝟙 _)) ≫
          (αT (Q.obj M) (Q.obj N) (Q.obj P)).hom)
    (M N P : C) {M' N' P' : T}
    (pM : Q.obj M ≅ M') (pN : Q.obj N ≅ N') (pP : Q.obj P ≅ P') :
    Q.map (αC M N P).hom ≫ b.hom.app (M, V.obj (N, P)) ≫
      I.map (Prod.mkHom pM.hom
        (b.hom.app (N, P) ≫ I.map (Prod.mkHom pN.hom pP.hom))) =
    b.hom.app (V.obj (M, N), P) ≫
      I.map (Prod.mkHom
        (b.hom.app (M, N) ≫ I.map (Prod.mkHom pM.hom pN.hom)) pP.hom) ≫
          (αT M' N' P').hom := by
  have hr := map_pair_comp I (𝟙 (Q.obj M)) (b.hom.app (N, P))
    pM.hom (I.map (Prod.mkHom pN.hom pP.hom))
  simp only [Category.id_comp] at hr
  rw [← hr]
  have hc' := hc M N P
  rw [← Category.assoc] at hc'
  rw [reassoc_of% hc']
  have hl := map_pair_comp I (b.hom.app (M, N)) (𝟙 (Q.obj P))
    (I.map (Prod.mkHom pM.hom pN.hom)) pP.hom
  simp only [Category.id_comp] at hl
  rw [← hl]
  simp only [Category.assoc]
  rw [hn]

private theorem reduced_square
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (p : F ⋙ Q ≅ R ⋙ H)
    {A B : C} {A' B' : D} {U V : S} {U' V' : T}
    (a : R.obj A ≅ U) (b : R.obj B ≅ V)
    (rA : Q.obj A' ≅ U') (rB : Q.obj B' ≅ V')
    (α : A ≅ B) (β : A' ≅ B') (γ : U ≅ V) (δ : U' ≅ V')
    (μA : F.obj A ≅ A') (μB : F.obj B ≅ B')
    (νA : H.obj U ≅ U') (νB : H.obj V ≅ V')
    (hα : R.map α.hom ≫ b.hom = a.hom ≫ γ.hom)
    (hβ : Q.map β.hom ≫ rB.hom = rA.hom ≫ δ.hom)
    (hμA : Q.map μA.hom ≫ rA.hom = p.hom.app A ≫ H.map a.hom ≫ νA.hom)
    (hμB : Q.map μB.hom ≫ rB.hom = p.hom.app B ≫ H.map b.hom ≫ νB.hom)
    (hν : H.map γ.hom ≫ νB.hom = νA.hom ≫ δ.hom) :
    F.map α.hom ≫ μB.hom = μA.hom ≫ β.hom := by
  apply Q.map_injective
  apply (cancel_mono rB.hom).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hμB]
  have hn := p.hom.naturality α.hom
  change Q.map (F.map α.hom) ≫ p.hom.app B = p.hom.app A ≫ H.map (R.map α.hom) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hα, H.map_comp]
  simp only [Category.assoc]
  rw [hν, hβ]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ δ.hom) hμA.symm

private theorem reduced_associativity
    {C D S T : Type*} [Category* C] [Category* D] [Category* S] [Category* T]
    (R : C ⥤ S) (Q : D ⥤ T) [Q.Faithful] (F : C ⥤ D) (H : S ⥤ T)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (J : S × S ⥤ S) (I : T × T ⥤ T)
    (a : U ⋙ R ≅ R.prod R ⋙ J) (b : V ⋙ Q ≅ Q.prod Q ⋙ I)
    (p : F ⋙ Q ≅ R ⋙ H) (ν : J ⋙ H ≅ H.prod H ⋙ I)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (αC : ∀ M N P, U.obj (U.obj (M, N), P) ≅ U.obj (M, U.obj (N, P)))
    (αD : ∀ M N P, V.obj (V.obj (M, N), P) ≅ V.obj (M, V.obj (N, P)))
    (αS : ∀ M N P, J.obj (J.obj (M, N), P) ≅ J.obj (M, J.obj (N, P)))
    (αT : ∀ M N P, I.obj (I.obj (M, N), P) ≅ I.obj (M, I.obj (N, P)))
    (hn : ∀ {M N P M' N' P' : T} (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P'),
      I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h) ≫ (αT M' N' P').hom =
        (αT M N P).hom ≫ I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
    (hC : ∀ M N P, R.map (αC M N P).hom ≫ a.hom.app (M, U.obj (N, P)) ≫
      J.map (Prod.mkHom (𝟙 _) (a.hom.app (N, P))) =
        a.hom.app (U.obj (M, N), P) ≫
          J.map (Prod.mkHom (a.hom.app (M, N)) (𝟙 _)) ≫
          (αS (R.obj M) (R.obj N) (R.obj P)).hom)
    (hD : ∀ M N P, Q.map (αD M N P).hom ≫ b.hom.app (M, V.obj (N, P)) ≫
      I.map (Prod.mkHom (𝟙 _) (b.hom.app (N, P))) =
        b.hom.app (V.obj (M, N), P) ≫
          I.map (Prod.mkHom (b.hom.app (M, N)) (𝟙 _)) ≫
          (αT (Q.obj M) (Q.obj N) (Q.obj P)).hom)
    (hμ : ∀ M N, Q.map (μ M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app (U.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        ν.hom.app (R.obj M, R.obj N))
    (hν : ∀ M N P, H.map (αS M N P).hom ≫
      ν.hom.app (M, J.obj (N, P)) ≫
        I.map (Prod.mkHom (𝟙 _) (ν.hom.app (N, P))) =
      ν.hom.app (J.obj (M, N), P) ≫
        I.map (Prod.mkHom (ν.hom.app (M, N)) (𝟙 _)) ≫
          (αT (H.obj M) (H.obj N) (H.obj P)).hom) (M N P : C) :
    F.map (αC M N P).hom ≫ (μ M (U.obj (N, P))).hom ≫
      V.map (Prod.mkHom (𝟙 _) (μ N P).hom) =
    (μ (U.obj (M, N)) P).hom ≫
      V.map (Prod.mkHom (μ M N).hom (𝟙 _)) ≫
        (αD (F.obj M) (F.obj N) (F.obj P)).hom := by
  let aL := a.app (U.obj (M, N), P) ≪≫
    J.mapIso (Iso.prod (a.app (M, N)) (Iso.refl _))
  let aR := a.app (M, U.obj (N, P)) ≪≫
    J.mapIso (Iso.prod (Iso.refl _) (a.app (N, P)))
  let bL := b.app (V.obj (F.obj M, F.obj N), F.obj P) ≪≫
    I.mapIso (Iso.prod
      (b.app (F.obj M, F.obj N) ≪≫ I.mapIso (Iso.prod (p.app M) (p.app N))) (p.app P))
  let bR := b.app (F.obj M, V.obj (F.obj N, F.obj P)) ≪≫
    I.mapIso (Iso.prod (p.app M)
      (b.app (F.obj N, F.obj P) ≪≫ I.mapIso (Iso.prod (p.app N) (p.app P))))
  let μL := μ (U.obj (M, N)) P ≪≫
    V.mapIso (Iso.prod (μ M N) (Iso.refl _))
  let μR := μ M (U.obj (N, P)) ≪≫
    V.mapIso (Iso.prod (Iso.refl _) (μ N P))
  let νL := ν.app (J.obj (R.obj M, R.obj N), R.obj P) ≪≫
    I.mapIso (Iso.prod (ν.app (R.obj M, R.obj N)) (Iso.refl _))
  let νR := ν.app (R.obj M, J.obj (R.obj N, R.obj P)) ≪≫
    I.mapIso (Iso.prod (Iso.refl _) (ν.app (R.obj N, R.obj P)))
  have he := reduced_square R Q F H p aL aR bL bR
    (αC M N P) (αD (F.obj M) (F.obj N) (F.obj P))
    (αS (R.obj M) (R.obj N) (R.obj P))
    (αT (H.obj (R.obj M)) (H.obj (R.obj N)) (H.obj (R.obj P))) μL μR νL νR
  suffices hh : F.map (αC M N P).hom ≫ μR.hom =
      μL.hom ≫ (αD (F.obj M) (F.obj N) (F.obj P)).hom by
    simpa only [μL, μR, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Category.assoc] using hh
  apply he
  · simpa only [aR, aL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Iso.app_hom, Category.assoc] using hC M N P
  · simpa only [bR, bL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.app_hom, Functor.comp_obj, Category.assoc] using
      transport_associator Q V I b αD αT hn hD _ _ _ (p.app M) (p.app N) (p.app P)
  · simpa only [μL, bL, aL, νL, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Functor.map_comp, Category.assoc] using
        nested_left R Q F H U V J I a b p ν μ hμ M N P
  · simpa only [μR, bR, aR, νR, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Functor.map_comp, Category.assoc] using
        nested_right R Q F H U V J I a b p ν μ hμ M N P
  · simpa only [νR, νL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Iso.app_hom, Category.assoc] using hν (R.obj M) (R.obj N) (R.obj P)


end ReductionCalculus

section CoherentReductionCache
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coherentReduction (W : Scheme.{u}) :
    sfIntegralConstructibleCategory l E W ⥤ coefficientSequenceDerived l E W :=
  (sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentReduction_fullyFaithful (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (coherentReduction l E W).Full ∧ (coherentReduction l E W).Faithful := by
  simpa only [coherentReduction, integralSystemReduction, pullbackTensorCalculus] using
    integralSystemReduction_fullyFaithful l E W
end CoherentReductionCache

section HigherCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The canonical completed composition family, normalized by every finite reduction.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (@constructibleIntegralPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY) ≅
      (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ Z X h hZ hX) :=
  (integralPullbackComposition l E).choose h f

/-- The canonical rational composition comparison on unchanged integral objects.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: localize the specified integral composition
  map and conjugate by the object equalities in rationalDerivedPullback_existsUnique. This fixes
  every component and its inverse, so the required isomorphism exists uniquely. -/
theorem pullbackTensorRationalComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).obj (((@rationalDerivedPullback l _ E _ _
        _ X Y f hX hY)).obj M),
      HEq e.hom ((sfRationalConstructibleLocalization l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M.obj)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.2.1 M)
      ?_
      ((sfRationalConstructibleLocalization l E Z).mapIso
        ((pullbackTensorIntegralComposition l E f h).app M.obj))
    have hf (K) : (rationalDerivedPullback l E f).obj K =
        ⟨(constructibleIntegralPullback l E f).obj K.obj⟩ :=
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
    have hh (K) : (rationalDerivedPullback l E h).obj K =
        ⟨(constructibleIntegralPullback l E h).obj K.obj⟩ :=
      (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.1 K
    rw [hh, hf]
    rfl

/-- Rationalization of the finite-reduction-normalized integral composition.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :=
  ((@pullbackTensorRationalComposition_existsUnique l _ E _ _ _ X Y Z f h hX hY hZ) M).exists.choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Common-stage composition, specified at every larger finite coefficient field.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: represent the rational composition at the
  stage of M. Conjugate by the three prescribed transition/pullback comparisons. Their scalar
  cocycles identify these representatives at every enlargement. The rational inverse gives an
  inverse class; the representative at the original stage determines the class uniquely. -/
theorem pullbackTensorCommonComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).obj (((@commonStageDerivedPullback l _
        Ω _ _ _ X Y f hX hY)).obj M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L),
        HEq e.hom (ofHom (commonStagePullbackObject l Ω (h ≫ f) M)
          (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M)) L hM hM
          ((commonStagePullbackComparison l Ω (h ≫ f) M L hM).hom ≫
            ((@pullbackTensorRationalComposition l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
              Y Z f h hX hY
              hZ)
              (M.toStage hM)).hom ≫
            ((@rationalDerivedPullback l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ Z
              X h hZ hX)).map
              (commonStagePullbackComparison l Ω f M L hM).inv ≫
            (commonStagePullbackComparison l Ω h
              (commonStagePullbackObject l Ω f M) L hM).inv)) := by
  sorry

/-- The composition isomorphism represented by the prescribed rational comparison.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  ((@pullbackTensorCommonComposition_existsUnique l _ Ω _ _ _ X Y Z f h hX hY hZ) M).exists.choose

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorRationalComposition pullbackTensorCommonComposition

/-- Composition equation on the actual canonical integral comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
          (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N)) =
    ((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
      (((@constructibleIntegralTensor l _ E _ _ _
      Y hY)).obj
      (M,N)) ≫
      ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
          N)).hom

/-- Composition equation on the actual canonical rational comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop :=
  ((@canonicalRationalPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@rationalDerivedTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ)
        M).hom) (((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ) N).hom)) =
    ((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ) (((@rationalDerivedTensor l
      _ E _ _ _ Y hY)).obj
      (M,N))).hom ≫
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).map ((@canonicalRationalPullbackTensor l
        _ E _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalRationalPullbackTensor l _ E _ _ _ Z X h hZ hX)
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M) (((@rationalDerivedPullback l _
          E _ _ _ X Y f hX hY)).obj N)).hom

/-- Composition equation on the actual canonical commonstage comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) : Prop :=
  ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
        M).hom) (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom)) =
    ((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) (((@commonStageDerivedTensor
      l _ Ω _ _ _ Y hY)).obj
      (M,N))).hom ≫
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
        ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom

/-- Reduction of the actual completed tensor via its fixed Roos realization and counit.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralReductionTensor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorCalculus l E W).reduction.obj
      (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)).obj ≅
    (pullbackTensorCalculus l E W).systemClosed.tensor.obj
      ((pullbackTensorCalculus l E W).reduction.obj M.obj,
       (pullbackTensorCalculus l E W).reduction.obj N.obj) :=
  (pullbackTensorCalculus l E W).reduction.mapIso
    ((pullbackTensorIntegralTensorModel l E W).app (M.obj,N.obj)) ≪≫
    @asIso _ _ _ _ ((pullbackTensorCalculus l E W).adjunction.counit.app
      ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E W).reduction.obj M.obj,
         (pullbackTensorCalculus l E W).reduction.obj N.obj)))
      (((@pullbackTensorComparisonCounits l _ E _ _ _ W W (𝟙 W) hW hW) M N).1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reduction of completed pullback via its actual normalized Roos model and counit.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralReductionPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorCalculus l E X).reduction.obj
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M).obj ≅
    (pullbackTensorSequenceDerived l E f).obj
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj) :=
  letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M M).2.1
  (pullbackTensorCalculus l E X).reduction.mapIso
    ((pullbackTensorIntegralPullbackModel l E f).app M.obj) ≪≫
    asIso ((pullbackTensorCalculus l E X).adjunction.counit.app _)

/-- The actual integral comparison reduces to the same coherent comparison at all levels.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  (pullbackTensorCalculus l E X).reduction.map
      ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom.hom ≫
    ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ X hX)
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
    (pullbackTensorCalculus l E X).systemClosed.tensor.map
      (Prod.mkHom ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY) M).hom
        ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY) N).hom) =
  ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY)
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
    (pullbackTensorSequenceDerived l E f).map
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ Y hY) M N).hom ≫
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
       (pullbackTensorCalculus l E Y).reduction.obj N.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralComparison_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    canonicalIntegralPullbackTensor_reduction l E f M N := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let := ((pullbackTensorComparisonCounits l E f) M N).1
    let := ((pullbackTensorComparisonCounits l E f) M N).2.1
    let := ((pullbackTensorComparisonCounits l E f) M N).2.2
    have hh := reduction_comparison
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction
      (pullbackTensorCalculus l E Y).reduction (coefficientSequenceLimit l E Y)
      (pullbackTensorCalculus l E Y).adjunction
      (integralDerivedPullback l E f) (pullbackTensorSequenceDerived l E f)
      (integralCompletedTensor l E Y) (integralCompletedTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (pullbackTensorIntegralPullbackModel l E f)
      (pullbackTensorIntegralTensorModel l E Y)
      (pullbackTensorIntegralTensorModel l E X)
      (pullbackTensorSystemComparison l E f) M.obj N.obj
    unfold canonicalIntegralPullbackTensor_reduction
    dsimp only [canonicalIntegralPullbackTensor, ObjectProperty.isoMk,
      ObjectProperty.homMk, pullbackTensorIntegralReductionTensor,
      pullbackTensorIntegralReductionPullback, pullbackTensorReferenceComparison,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Iso.prod_hom, Functor.prod_map, Functor.comp_map,
      pullbackTensorReferencePullback, pullbackTensorReferenceTensor,
      constructibleIntegralPullback, constructibleIntegralTensor,
      ObjectProperty.lift, ObjectProperty.ι_obj, Functor.comp_obj, Functor.prod_obj,
      Functor.id_obj]
    simpa only [Functor.map_comp, Category.assoc, Iso.prod_hom, Iso.symm_hom,
      Iso.app_inv, asIso_inv, Functor.comp_map, Functor.prod_map, Functor.id_obj] using hh


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def reduction_tensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙ coherentReduction l E W ≅
      (coherentReduction l E W).prod (coherentReduction l E W) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E W MN.1 MN.2) (by
    intro MN PQ k
    dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
      counit_model_naturality
        (pullbackTensorCalculus l E W).reduction (coefficientSequenceLimit l E W)
        (pullbackTensorCalculus l E W).adjunction (integralCompletedTensor l E W)
        (((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction) ⋙
          (pullbackTensorCalculus l E W).systemClosed.tensor)
        (pullbackTensorIntegralTensorModel l E W) (Prod.mkHom k.1.hom k.2.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def reduction_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ coherentReduction l E X ≅
      coherentReduction l E Y ⋙ pullbackTensorSequenceDerived l E f :=
  NatIso.ofComponents (pullbackTensorIntegralReductionPullback l E f) (by
    intro M N k
    dsimp only [pullbackTensorIntegralReductionPullback, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralPullback, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, pullbackTensorCalculus] using counit_model_naturality
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction (integralDerivedPullback l E f)
      ((pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f)
      (pullbackTensorIntegralPullbackModel l E f) k.hom)

attribute [local irreducible] pullbackTensorIntegralReductionTensor
  pullbackTensorIntegralReductionPullback

/-- The integral associator is uniquely fixed in the coherent reduction category.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Reduction is fully faithful on
  derived-complete constructible objects: its unit is invertible by normalized DVR effectivity.
  Conjugate the specified coherent tensor associator by the actual reduction/tensor comparisons and
  lift along that fully faithful functor. Lift the inverse too; faithfulness gives the inverse
  identities and uniqueness. -/
theorem pullbackTensorIntegralAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (((@constructibleIntegralTensor l _
      E _ _ _ W hW)).obj (M,N),P)
      ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,((@constructibleIntegralTensor l _ E
        _ _ _ W hW)).obj (N,P)),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M
          (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,P))).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N P).hom) =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW)
        (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)) P).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom (𝟙 _)) ≫
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator
          ((pullbackTensorCalculus l E W).reduction.obj M.obj)
          ((pullbackTensorCalculus l E W).reduction.obj N.obj)
          ((pullbackTensorCalculus l E W).reduction.obj P.obj)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    simpa only [coherentReduction, Functor.comp_map, ObjectProperty.ι_map,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Category.assoc] using
      existsUnique_iso_of_map_constraints (coherentReduction l E W)
      (A := (constructibleIntegralTensor l E W).obj
        ((constructibleIntegralTensor l E W).obj (M,N),P))
      (B := (constructibleIntegralTensor l E W).obj
        (M,(constructibleIntegralTensor l E W).obj (N,P)))
      (pullbackTensorIntegralReductionTensor l E W
        ((constructibleIntegralTensor l E W).obj (M,N)) P)
      ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
        (Iso.prod (pullbackTensorIntegralReductionTensor l E W M N) (Iso.refl _)))
      ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator _ _ _)
      (pullbackTensorIntegralReductionTensor l E W M
        ((constructibleIntegralTensor l E W).obj (N,P)))
      ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
        (Iso.prod (Iso.refl _) (pullbackTensorIntegralReductionTensor l E W N P)))

/-- The canonical completed associator, fixed by its coherent reduction.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralAssociator_existsUnique l _ E _ _ _ W hW) M N P).exists.choose

/-- The rational associator is the actual localization of the integral map.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the object equalities in
  rationalDerivedTensor_existsUnique to identify the endpoints. Localize the preceding integral
  isomorphism and its inverse. The displayed equality fixes its hom, so the isomorphism is unique.
-/
theorem pullbackTensorRationalAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (((@rationalDerivedTensor l _ E _ _ _ W
      hW)).obj (M,N),P) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,((@rationalDerivedTensor l _ E _ _ _ W
        hW)).obj (N,P)),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralAssociator l _ E _ _ _ W hW) M.obj N.obj P.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hT (MN) : (rationalDerivedTensor l E W).obj MN =
        ⟨(constructibleIntegralTensor l E W).obj (MN.1.obj,MN.2.obj)⟩ :=
      (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 MN
    apply existsUnique_iso_of_eq ?_ ?_
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralAssociator l E W M.obj N.obj P.obj))
    · rw [hT, hT]
      rfl
    · rw [hT, hT]
      rfl

/-- The localized integral associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalAssociator_existsUnique l _ E _ _ _ W hW) M N P).exists.choose

/-- The integral braiding is uniquely fixed in the coherent reduction category.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Reduction is fully faithful on
  derived-complete constructible objects: its unit is invertible by normalized DVR effectivity.
  Conjugate the specified coherent tensor Koszul symmetry by the actual reduction/tensor comparisons
  and lift along that fully faithful functor. Lift the inverse too; faithfulness gives the inverse
  identities and uniqueness. -/
theorem pullbackTensorIntegralBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,M),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N M).hom =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    simpa only [coherentReduction, Functor.comp_map, ObjectProperty.ι_map,
      Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Category.assoc] using
      existsUnique_iso_of_map_constraint (coherentReduction l E W)
      (A := (constructibleIntegralTensor l E W).obj (M,N))
      (B := (constructibleIntegralTensor l E W).obj (N,M))
      (pullbackTensorIntegralReductionTensor l E W M N)
      ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel).app
          ((pullbackTensorCalculus l E W).reduction.obj M.obj,
            (pullbackTensorCalculus l E W).reduction.obj N.obj))
      (pullbackTensorIntegralReductionTensor l E W N M)

/-- The canonical completed braiding, fixed by its coherent reduction.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralBraiding_existsUnique l _ E _ _ _ W hW) M N).exists.choose

/-- The rational braiding is the actual localization of the integral map.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the object equalities in
  rationalDerivedTensor_existsUnique to identify the endpoints. Localize the preceding integral
  isomorphism and its inverse. The displayed equality fixes its hom, so the isomorphism is unique.
-/
theorem pullbackTensorRationalBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (N,M),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralBraiding l _ E _ _ _ W hW) M.obj N.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (M,N))
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (N,M))
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralBraiding l E W M.obj N.obj))

/-- The localized integral braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalBraiding_existsUnique l _ E _ _ _ W hW) M N).exists.choose

/-- The left nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonLeft (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W
      (commonStageTensorObject l Ω W M N) P).stage ≤ L) :=
  commonStageTensorComparison l Ω W (commonStageTensorObject l Ω W M N) P L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (commonStageTensorComparison l Ω W M N L (((Padic.finiteCoefficientFields_properties
        l Ω).1 (commonStageTensorObject l Ω W M N).stage P.stage).1.trans h)) (Iso.refl _))

/-- The right nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonRight (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W M
      (commonStageTensorObject l Ω W N P)).stage ≤ L) :=
  commonStageTensorComparison l Ω W M (commonStageTensorObject l Ω W N P) L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (Iso.refl _) (commonStageTensorComparison l Ω W N P L
        (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage (commonStageTensorObject l Ω W N
        P).stage).2.trans h)))

attribute [local irreducible] pullbackTensorCommonLeft pullbackTensorCommonRight

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage associator has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the rational associator by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  sorry

/-- The stage-independent rational associator class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonAssociator_existsUnique l _ Ω _ _ _ W hW) M N P).exists.choose

attribute [local irreducible] pullbackTensorCommonAssociator

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage braiding has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the rational braiding by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,N) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (N,M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W M N).stage ≤ L) (hT : (commonStageTensorObject l Ω W N
          M).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M N)
          (commonStageTensorObject l Ω W N M) L hS hT
          ((commonStageTensorComparison l Ω W M N L hS).hom ≫
            ((@pullbackTensorRationalBraiding l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                hS)) (N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                N.stage).2.trans hS))).hom ≫
            (commonStageTensorComparison l Ω W N M L hT).inv)) := by
  sorry

/-- The stage-independent rational braiding class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonBraiding_existsUnique l _ Ω _ _ _ W hW) M N).exists.choose

private theorem normalizedCoefficientSequence_of_iso (W : Scheme.{u})
    {A B : coefficientSequenceDerived l E W} (e : B ≅ A)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro m n h P
    let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
    let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
    let R := normalizedDVRRes l E W h
    have ht := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
    change em.hom ≫ _ = _ ≫ R.map en.hom at ht
    have hti := (coefficientSequenceDerivedTransition l E W h).naturality e.inv
    change em.inv ≫ _ = _ ≫ R.map en.inv at hti
    constructor
    · intro f g hfg
      apply (cancel_epi en.inv).mp
      apply (hA h P).injective
      change _ ≫ R.map (en.inv ≫ f) = _ ≫ R.map (en.inv ≫ g)
      have hh (k : (coefficientSequenceDerivedEvaluation l E W n).obj B ⟶ P) :
          (coefficientSequenceDerivedTransition l E W h).app A ≫ R.map (en.inv ≫ k) =
            em.inv ≫ (coefficientSequenceDerivedTransition l E W h).app B ≫ R.map k := by
        rw [Functor.map_comp, ← Category.assoc, ← hti, Category.assoc]
      rw [hh, hh]
      exact congrArg (fun k ↦ em.inv ≫ k) hfg
    · intro a
      obtain ⟨b, hb⟩ := (hA h P).surjective (em.inv ≫ a)
      refine ⟨en.hom ≫ b, ?_⟩
      change _ ≫ R.map (en.hom ≫ b) = a
      change _ ≫ R.map b = em.inv ≫ a at hb
      rw [Functor.map_comp, ← Category.assoc, ← ht, Category.assoc, hb]
      simp

private theorem pullbackTensorSystemUnit_normalized (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    IsNormalizedCoefficientSequence l E W
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨M, hM⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    let e : (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
        CompletedOperations.unit l E (W := fun _ : Unit ↦ W) () :=
      closedTensorUnitIso
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed
        (M.system ()).closed ≪≫
        (M.system ()).unitIso
    intro m n h P
    exact normalizedCoefficientSequence_of_iso l E W e
      (fun {m n} h P ↦ hM.unit () h P) h P

private def pushUnitIso {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r})
    {S : Sheaf J RingCat.{r}}
    (h : (F.sheafPushforwardContinuous RingCat.{r} J K).obj R = S) :
    (SheafOfModules.pushforward (F := F) (eqToHom h.symm)).obj
      (SheafOfModules.unit R) ≅ SheafOfModules.unit S := by
  subst S
  exact Iso.refl _

private def evaluationUnitIso (W : Scheme.{u}) (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).obj
      (SheafOfModules.unit
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W))) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) :=
  pushUnitIso (Prod.sectR n W.ProEt) _ (coefficientSequenceEvaluationRing_eq l E W n)

private theorem systemUnitEvaluationIso (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] (n : ℕ) :
    Nonempty ((coefficientSequenceDerivedEvaluation l E W n).obj
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed.monoidal.tensorUnit ≅
      finiteConstantCoefficientObject l E W n) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨M, hM⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    let e := closedTensorUnitIso
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed
      (M.system ()).closed ≪≫ (M.system ()).unitIso
    exact ⟨(coefficientSequenceDerivedEvaluation l E W n).mapIso e ≪≫
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (evaluationUnitIso l E W n)⟩


/-- The limit of the coherent ring unit is constructible and complete.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: The coherent ring unit is the constant
  rank-one finite coefficient tower. Its quotient transitions are normalized. Normalized DVR
  effectivity computes its limit as the completed rank-one coefficient module, whose reductions are
  the finite constructible ring units; these have uniform amplitude zero. -/
theorem pullbackTensorIntegralUnit_constructible (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let S := (coefficientDerivedSystemEvaluationCalculus l E W).choose
    let U := S.systemClosed.monoidal.tensorUnit
    let K := (coefficientSequenceLimit l E W).obj U
    have hl := coefficientPrime_isUnit l W
    have hn : IsNormalizedCoefficientSequence l E W U :=
      fun {m n} h P ↦ pullbackTensorSystemUnit_normalized l E W h P
    obtain ⟨hcomplete, hcounit⟩ := (purNormalizedReconstruction l E W hl S).1 U hn
    obtain ⟨D, hlp, hD⟩ := hcomplete
    refine ⟨(sfDerivedComplete_iff_legacy l E W D hlp K).mpr hD,
      0, 0, le_refl _, ?_⟩
    intro n
    let := hcounit
    obtain ⟨en⟩ := systemUnitEvaluationIso l E W n
    let e : (scalarReductionDerivedExtension l E W n).obj K ≅
        finiteConstantCoefficientObject l E W n :=
      (S.reductionEvaluation n).symm.app K ≪≫
        (coefficientSequenceDerivedEvaluation l E W n).mapIso
          (asIso (S.adjunction.counit.app U)) ≪≫ en
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) W) :=
      (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated W
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨ObjectProperty.prop_of_iso _ e.symm
      (finiteConstantCoefficient_constructible l E W n).1, ?_⟩
    intro i hi
    have hi' : i ∈ proEtaleCohomologicalSupport
        (finiteConstantCoefficientObject l E W n) := by
      intro hz
      exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mpr hz)
    have he : i = 0 := by
      by_contra h
      apply hi'
      unfold finiteConstantCoefficientObject
      rcases lt_or_gt_of_ne h with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 i h
      · exact DerivedCategory.isZero_of_isLE _ 0 i h
    simp [he]

/-- The actual derived limit of the coherent coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] : sfIntegralConstructibleCategory l E W :=
  ⟨_, @pullbackTensorIntegralUnit_constructible l _ E _ _ _ W hW⟩

/-- The reduction counit of the normalized coefficient-ring unit is invertible.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: The finite ring units and their quotient
  tensor comparisons form a normalized system. Apply normalized DVR effectivity to this system. The
  reconstruction isomorphism is precisely the reduction/limit adjunction counit. -/
theorem pullbackTensorIntegralUnit_counit (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] : IsIso ((pullbackTensorCalculus l E
      W).adjunction.counit.app
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hl := coefficientPrime_isUnit l W
    exact ((purNormalizedReconstruction l E W hl
      (coefficientDerivedSystemEvaluationCalculus l E W).choose).1 _
        (fun {m n} h P ↦ pullbackTensorSystemUnit_normalized l E W h P)).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed identification of the reduced integral unit with the coherent ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralUnitReduction (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    (pullbackTensorCalculus l E W).reduction.obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W
      hW)).obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit :=
  letI := (@pullbackTensorIntegralUnit_counit l _ E _ _ _ W hW)
  asIso ((pullbackTensorCalculus l E W).adjunction.counit.app _)

/-- The rational unit is the localization of the completed coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (sfRationalConstructibleLocalization l E W).obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W hW))

attribute [local irreducible] pullbackTensorIntegralUnitReduction

-- Keep the category instances folded after constructing the unit evaluation map.
set_option allowUnsafeReducibility true in
attribute [local irreducible] instCategoryDerivedCategory DerivedCategory.instPreadditive
  SheafOfModules.instAbelian SheafOfModules.instCategory

/-- The integral left unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the coherent unitor by the actual
  tensor-reduction and unit-reduction isomorphisms. Reduction is fully faithful on the complete
  constructible subcategory by normalized effectivity, so this arrow and its inverse lift uniquely.
  Faithfulness gives the inverse identities. -/
theorem pullbackTensorIntegralLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorIntegralUnit l _ E
      _ _ _ W hW),M) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) ((@pullbackTensorIntegralUnit l _
          E _ _ _ W hW)) M).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    let target : (coherentReduction l E W).obj
        ((constructibleIntegralTensor l E W).obj (pullbackTensorIntegralUnit l E W,M)) ≅
        (coherentReduction l E W).obj M :=
      pullbackTensorIntegralReductionTensor l E W (pullbackTensorIntegralUnit l E W) M ≪≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod (pullbackTensorIntegralUnitReduction l E W) (Iso.refl _)) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor _
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map (coherentReduction l E W) target
    refine ⟨d, ?_, ?_⟩
    · change (coherentReduction l E W).map
        d.hom = _
      rw [hd]
      rfl
    · intro d' hd'
      apply hu
      exact hd'

/-- The normalized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational left unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the prescribed rational tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorRationalUnit l _ E _ _ _
      W hW),M) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
        (pullbackTensorRationalUnit l E W,M)) rfl
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralLeftUnitor l E W M.obj))

/-- The localized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The integral right unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the coherent unitor by the actual
  tensor-reduction and unit-reduction isomorphisms. Reduction is fully faithful on the complete
  constructible subcategory by normalized effectivity, so this arrow and its inverse lift uniquely.
  Faithfulness gives the inverse identities. -/
theorem pullbackTensorIntegralRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorIntegralUnit l _
      E _ _ _ W hW)) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M ((@pullbackTensorIntegralUnit l
          _ E _ _ _ W hW))).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    let target : (coherentReduction l E W).obj
        ((constructibleIntegralTensor l E W).obj (M,pullbackTensorIntegralUnit l E W)) ≅
        (coherentReduction l E W).obj M :=
      pullbackTensorIntegralReductionTensor l E W M (pullbackTensorIntegralUnit l E W) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod (Iso.refl _) (pullbackTensorIntegralUnitReduction l E W)) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor _
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map (coherentReduction l E W) target
    refine ⟨d, ?_, ?_⟩
    · change (coherentReduction l E W).map
        d.hom = _
      rw [hd]
      rfl
    · intro d' hd'
      apply hu
      exact hd'

/-- The normalized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational right unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the prescribed rational tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorRationalUnit l _ E _ _
      _ W hW)) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
        (M,pullbackTensorRationalUnit l E W)) rfl
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralRightUnitor l E W M.obj))

/-- The localized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

attribute [local irreducible] pullbackTensorIntegralUnit pullbackTensorRationalUnit
  pullbackTensorIntegralLeftUnitor pullbackTensorIntegralRightUnitor
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar extension preserves the canonical rational coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: For integral coefficients, scalar extension
  sends the coefficient-ring unit to the new coefficient ring by multiplication. Its unit equations
  hold on pure tensors, remain true in both Roos coordinates, and localize. The tensor comparison is
  invertible; cancellation in the unit square at the unit object proves uniqueness. -/
theorem pullbackTensorRationalScalarUnit_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃! e : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((@pullbackTensorRationalUnit l _ E _ _ _ W hW)) ≅ (@pullbackTensorRationalUnit l _ L _ _
            _ W hW),
      ∀ M : sfRationalConstructibleCategory l E W,
        ((rationalTensorScalarComparison l E L ι W).hom.app ((@pullbackTensorRationalUnit l _ E _ _
          _ W hW),M) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom e.hom (𝟙 _)) ≫
          ((@pullbackTensorRationalLeftUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalLeftUnitor l
              _ E _ _ _ W hW) M).hom) ∧
        ((rationalTensorScalarComparison l E L ι W).hom.app (M,(@pullbackTensorRationalUnit l _ E _
          _ _ W hW)) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom (𝟙 _) e.hom) ≫
          ((@pullbackTensorRationalRightUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalRightUnitor l
              _ E _ _ _ W hW) M).hom) := by
  sorry

/-- The coefficient-ring scalar comparison fixed by the two tensor unit squares.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalScalarUnit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (@pullbackTensorRationalScalarUnit_existsUnique l _ E _ _ _ L _ _ _ ι W hW).exists.choose

/-- The common-stage unit represented over the least finite coefficient field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
      generalAlgebraicallyClosedConstructibleCategory l
      Ω W :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (@pullbackTensorRationalUnit l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) _ _ _ W hW)⟩

/-- The common-stage ring unit is the rational ring unit at every larger stage.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonUnitStage (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage ≤ L) :
    ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).toStage h ≅
      (@pullbackTensorRationalUnit l _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W hW)
        :=
  (operationStageTransitionIso l Ω W _ L h).app _ ≪≫
    @pullbackTensorRationalScalarUnit l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) _ _ _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.coefficientInclusion l Ω _ L h) W hW

attribute [local irreducible] pullbackTensorCommonUnitStage pullbackTensorCommonUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage left unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Represent at the finite compositum. Apply
  the tensor-stage comparison, the coefficient-ring unit comparison, and the rational unitor. The
  scalar unit equations and scalar cocycles identify these arrows at all larger stages. Their
  inverses define an inverse class, and this representative condition determines the colimit hom
  uniquely. -/
theorem pullbackTensorCommonLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)),M) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW)) M) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω _ _ _
            W hW)).stage
          M.stage).2.trans h)
          ((commonStageTensorComparison l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω
                  _ _ _ W hW)).stage M.stage).1.trans h)).hom (𝟙 _)) ≫
            ((@pullbackTensorRationalLeftUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage M.stage).2.trans h))).hom)) :=
                  by
  sorry

/-- The common-stage class of the canonical rational left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonLeftUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage right unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Represent at the finite compositum. Apply
  the tensor-stage comparison, the coefficient-ring unit comparison, and the rational unitor. The
  scalar unit equations and scalar cocycles identify these arrows at all larger stages. Their
  inverses define an inverse class, and this representative condition determines the colimit hom
  uniquely. -/
theorem pullbackTensorCommonRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (M,((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW))) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage ((@pullbackTensorCommonUnit l _
            Ω _ _ _ W hW)).stage).1.trans h)
          ((commonStageTensorComparison l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom (𝟙 _) ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                  ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).2.trans h)).hom) ≫
            ((@pullbackTensorRationalRightUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).1.trans h))).hom)) := by
  sorry

/-- The common-stage class of the canonical rational right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonRightUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

/-- Both unit equations for the actual canonical integral comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
    ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
      (@pullbackTensorIntegralUnit l _ E _ _ _ X hX),
    ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) ((@pullbackTensorIntegralUnit l _
        E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX) (((@constructibleIntegralPullback l _
          E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M ((@pullbackTensorIntegralUnit l
        _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX) (((@constructibleIntegralPullback l _
          E _ _ _ X Y f hX hY)).obj M)).hom
          =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom)

/-- Both unit equations for the actual canonical rational comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj ((@pullbackTensorRationalUnit l _
    E _ _ _ Y hY)) ≅
      (@pullbackTensorRationalUnit l _ E _ _ _ X hX),
    ∀ M : sfRationalConstructibleCategory l E Y,
      (((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) ((@pullbackTensorRationalUnit l _
        E _ _ _ Y hY)) M).hom ≫
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorRationalLeftUnitor l _ E _ _ _ X hX) (((@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalLeftUnitor l
        _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M ((@pullbackTensorRationalUnit l
        _ E _ _ _ Y hY))).hom ≫
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorRationalRightUnitor l _ E _ _ _ X hX) (((@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalRightUnitor
        l _ E _ _ _ Y hY) M).hom)

/-- Both unit equations for the actual canonical commonstage comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj ((@pullbackTensorCommonUnit l _
    Ω _ _ _ Y hY)) ≅
      (@pullbackTensorCommonUnit l _ Ω _ _ _ X hX),
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) ((@pullbackTensorCommonUnit l
        _ Ω _ _ _ Y hY)) M).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorCommonLeftUnitor l _ Ω _ _ _ X hX) (((@commonStageDerivedPullback l _ Ω _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonLeftUnitor
        l _ Ω _ _ _ Y hY) M).hom) ∧
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M ((@pullbackTensorCommonUnit
        l _ Ω _ _ _ Y hY))).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorCommonRightUnitor l _ Ω _ _ _ X hX) (((@commonStageDerivedPullback l _ Ω _
          _ _ X Y f hX hY)).obj M)).hom =
      ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonRightUnitor
        l _ Ω _ _ _ Y hY) M).hom)

/-- Coherence for the canonical integral comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
      ((@pullbackTensorIntegralAssociator l _ E _ _ _ Y hY) M N P).hom ≫
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
            (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (N,P))).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom (𝟙 _) ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) N P).hom)
              =
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
          (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N)) P).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom (𝟙 _))
              ≫
          ((@pullbackTensorIntegralAssociator l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj P)).hom

/-- The normalized integral comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalIntegralPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E X).2
    apply reduced_associativity
      (coherentReduction l E Y) (coherentReduction l E X)
      (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (reduction_tensor l E Y) (reduction_tensor l E X) (reduction_pullback l E f)
      (pullbackTensorSystemComparison l E f) (canonicalIntegralPullbackTensor l E f)
      (pullbackTensorIntegralAssociator l E Y) (pullbackTensorIntegralAssociator l E X)
      (pullbackTensorCalculus l E Y).systemClosed.monoidal.associator
      (pullbackTensorCalculus l E X).systemClosed.monoidal.associator
    · intro M N P M' N' P' a b c
      exact @MonoidalCategory.associator_naturality _ _
        (pullbackTensorCalculus l E X).systemClosed.monoidal _ _ _ _ _ _ a b c
    · intro M N P
      exact (pullbackTensorIntegralAssociator_existsUnique l E Y M N P).exists.choose_spec
    · intro M N P
      exact (pullbackTensorIntegralAssociator_existsUnique l E X M N P).exists.choose_spec
    · exact integralComparison_reduction l E f
    · exact pullbackTensorSystemComparison_associativity l E f

/-- Coherence for the canonical rational comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalAssociator l _
      E _ _ _ Y hY) M N P).hom ≫
            ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M
              (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (N,P))).hom ≫
            ((@rationalDerivedTensor l _ E _ _ _ X hX)).map
              (Prod.mkHom (𝟙 _) ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) N
                P).hom) =
          ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY)
            (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) P).hom ≫
            ((@rationalDerivedTensor l _ E _ _ _ X hX)).map
              (Prod.mkHom ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom (𝟙
                _)) ≫
            ((@pullbackTensorRationalAssociator l _ E _ _ _ X hX)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj P)).hom

attribute [local irreducible] pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator canonicalIntegralPullbackTensor

section RationalCoherenceElaboration
attribute [local irreducible] sfIntegralConstructible Linear.homModule Preadditive.homGroup

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalRationalPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY) := by
  intro M N P
  let F := rationalDerivedPullback l E f
  let I := constructibleIntegralPullback l E f
  let Q := sfRationalConstructibleLocalization l E X
  have hF (K) : F.obj K =
      (sfRationalConstructibleLocalization l E X).obj (I.obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
  have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
      (sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralTensor l E Y).obj (MN.1.obj,MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1 MN
  have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
      Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj,MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
  have hmap {A B : sfRationalConstructibleCategory l E Y}
      {A' B' : sfIntegralConstructibleCategory l E Y}
      (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
      (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
      (a : A ⟶ B) (b : A' ⟶ B')
      (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
      HEq (F.map a) (Q.map (I.map b)) := by
    exact map_localized_heq I F (sfRationalConstructibleLocalization l E Y) Q
      (fun {K L} c ↦
        (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K L c 1)
      hA hB a b hab
  have hbase (K) : (F.obj K).obj = I.obj K.obj := by rw [hF]; rfl
  have hty (A B : sfRationalConstructibleCategory l E Y) :
      ((rationalDerivedTensor l E Y).obj (A,B)).obj =
        (constructibleIntegralTensor l E Y).obj (A.obj,B.obj) := by rw [hTY]; rfl
  have htx (A B : sfRationalConstructibleCategory l E X) :
      ((rationalDerivedTensor l E X).obj (A,B)).obj =
        (constructibleIntegralTensor l E X).obj (A.obj,B.obj) := by rw [hTX]; rfl
  have htmap {A B C D : sfRationalConstructibleCategory l E X}
      {A' B' C' D' : sfIntegralConstructibleCategory l E X}
      (hA : A = Q.obj A') (hB : B = Q.obj B')
      (hC : C = Q.obj C') (hD : D = Q.obj D')
      (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
      (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
      HEq ((rationalDerivedTensor l E X).map (Prod.mkHom a b))
        (Q.map ((constructibleIntegralTensor l E X).map (Prod.mkHom a' b'))) := by
    subst A B C D
    have ha' := eq_of_heq ha
    have hb' := eq_of_heq hb
    subst a b
    obtain ⟨bil, hbil, hbil'⟩ :=
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.2
        (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
    change HEq ((rationalDerivedTensor_existsUnique l E X).exists.choose.map
      (Prod.mkHom (Q.map a') (Q.map b'))) _
    rw [hbil]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [one_mul, Q, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using hbil' a' b' 1 1
  have hc (A B B' : sfIntegralConstructibleCategory l E Y) (h : B = B') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E f A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E f A B').hom) := by
    subst B'
    rfl
  have ha := (pullbackTensorRationalAssociator_existsUnique l E Y M N P).exists.choose_spec
  have ha' := hmap (by rw [hTY, hTY]; rfl) (by rw [hTY, hTY]; rfl) _ _ ha
  have hmid := (canonicalRationalPullbackTensor_existsUnique l E f M
    ((rationalDerivedTensor l E Y).obj (N,P))).exists.choose_spec
  have hmid' : HEq ((canonicalRationalPullbackTensor l E f M
      ((rationalDerivedTensor l E Y).obj (N,P))).hom)
      (Q.map (canonicalIntegralPullbackTensor l E f M.obj
        ((constructibleIntegralTensor l E Y).obj (N.obj,P.obj))).hom) :=
    hmid.trans (hc M.obj _ _ (hty N P))
  have hnp := (canonicalRationalPullbackTensor_existsUnique l E f N P).exists.choose_spec
  have hid : HEq (𝟙 (F.obj M)) (Q.map (𝟙 (I.obj M.obj))) := by
    have hh {A : sfRationalConstructibleCategory l E X}
        {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hF M)
  have hnp' := htmap (hF M) (hF M) (by rw [hF, hTY]; rfl)
    (by rw [hTX, hF, hF]; rfl) (𝟙 (F.obj M)) _ _ _ hid hnp
  have hleft₁ := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hF, hTY, hTY]; rfl) (by rw [hTX, hF, hF, hTY]; rfl) ha' hmid'
  have hleft := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hF, hF, hTY]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hleft₁ hnp'
  have hmn := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
  have hrmid := (canonicalRationalPullbackTensor_existsUnique l E f
    ((rationalDerivedTensor l E Y).obj (M,N)) P).exists.choose_spec
  have hc' (A A' B : sfIntegralConstructibleCategory l E Y) (h : A = A') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E f A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E f A' B).hom) := by
    subst A'
    rfl
  have hrmid' := hrmid.trans (hc' _ _ P.obj (hty M N))
  have hid' : HEq (𝟙 (F.obj P)) (Q.map (𝟙 (I.obj P.obj))) := by
    have hh {A : sfRationalConstructibleCategory l E X}
        {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hF P)
  have hmn' := htmap (by rw [hF, hTY]; rfl)
    (by rw [hTX, hF, hF]; rfl) (hF P) (hF P) _ (𝟙 (F.obj P)) _ _ hmn hid'
  have hrassoc := (pullbackTensorRationalAssociator_existsUnique l E X
    (F.obj M) (F.obj N) (F.obj P)).exists.choose_spec
  have has {A B C A' B' C' : sfIntegralConstructibleCategory l E X}
      (hA : A = A') (hB : B = B') (hC : C = C') :
      HEq (Q.map (pullbackTensorIntegralAssociator l E X A B C).hom)
        (Q.map (pullbackTensorIntegralAssociator l E X A' B' C').hom) := by
    subst A' B' C'
    rfl
  have hrassoc' := hrassoc.trans (has (hbase M) (hbase N) (hbase P))
  have hright₁ := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hF, hTY, hF]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hrmid' hmn'
  have hright := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hright₁ hrassoc'
  simp only [← Category.assoc]
  apply eq_of_heq
  simp only [← Functor.map_comp] at hleft hright
  have hh := canonicalIntegralPullbackTensor_associative_spec l E f M.obj N.obj P.obj
  simp only [← Category.assoc] at hh
  simpa only [pullbackTensorRationalAssociator, canonicalRationalPullbackTensor, F] using
    hleft.trans ((heq_of_eq (congrArg Q.map hh)).trans hright.symm)

/-- Coherence for the canonical commonstage comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonAssociator l
      _ Ω _ _ _ Y hY) M N P).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M
              (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (N,P))).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map
              (Prod.mkHom (𝟙 _) ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) N
                P).hom) =
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY)
            (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M,N)) P).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map
              (Prod.mkHom ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom (𝟙
                _)) ≫
            ((@pullbackTensorCommonAssociator l _ Ω _ _ _ X hX)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj P)).hom

/-- The normalized commonstage comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalCommonStagePullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalCommonStagePullbackTensor_associative l _ Ω _ _ _ X Y f hX hY) := by
  sorry

/-- Coherence for the canonical integral comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorIntegralBraiding
      l _ E _ _ _ Y hY) M N).hom ≫
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorIntegralBraiding l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized integral comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalIntegralPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E X).2
    let p := reduction_pullback l E f
    exact reduced_braiding
      (coherentReduction l E Y) (coherentReduction l E X)
      (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (pullbackTensorIntegralReductionTensor l E Y)
      (pullbackTensorIntegralReductionTensor l E X) p
      (canonicalIntegralPullbackTensor l E f)
      (fun M N ↦ (pullbackTensorSystemComparison l E f).app (M, N))
      (pullbackTensorIntegralBraiding l E Y) (pullbackTensorIntegralBraiding l E X)
      (fun M N ↦ (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel).app (M, N))
      (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).systemTensorModel)
      (fun M N ↦ (pullbackTensorIntegralBraiding_existsUnique l E Y M N).exists.choose_spec)
      (fun M N ↦ (pullbackTensorIntegralBraiding_existsUnique l E X M N).exists.choose_spec)
      (integralComparison_reduction l E f) (pullbackTensorSystemComparison_braiding l E f)


/-- Coherence for the canonical rational comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalBraiding l _ E
      _ _ _ Y hY) M N).hom ≫
            ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorRationalBraiding l _ E _ _ _ X hX)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalRationalPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro M N
    let F := rationalDerivedPullback l E f
    let I := constructibleIntegralPullback l E f
    let Q := sfRationalConstructibleLocalization l E X
    have hF (K) : F.obj K =
        (sfRationalConstructibleLocalization l E X).obj (I.obj K.obj) :=
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
    have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
        (sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralTensor l E Y).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1 MN
    have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
        Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
    have hm : (F.obj M).obj = I.obj M.obj := by
      rw [hF]
      rfl
    have hn : (F.obj N).obj = I.obj N.obj := by
      rw [hF]
      rfl
    have hmap {A B : sfRationalConstructibleCategory l E Y}
        {A' B' : sfIntegralConstructibleCategory l E Y}
        (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
        (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
        (a : A ⟶ B) (b : A' ⟶ B')
        (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
        HEq (F.map a) (Q.map (I.map b)) := by
      exact map_localized_heq I F (sfRationalConstructibleLocalization l E Y) Q
        (fun {K L} c ↦
          (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K L c 1)
        hA hB a b hab
    have hb := (pullbackTensorRationalBraiding_existsUnique l E Y M N).exists.choose_spec
    have hb' := hmap (hTY (M,N)) (hTY (N,M)) _ _ hb
    have hc := (canonicalRationalPullbackTensor_existsUnique l E f N M).exists.choose_spec
    have hleft := heq_comp
      (by rw [hF, hTY]; rfl)
      (by rw [hF, hTY]; rfl)
      (by rw [hTX, hF, hF]; rfl) hb' hc
    have hd := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
    have he := (pullbackTensorRationalBraiding_existsUnique l E X
      (F.obj M) (F.obj N)).exists.choose_spec
    have hsym {A B A' B' : sfIntegralConstructibleCategory l E X}
        (hA : A = A') (hB : B = B') :
        HEq (Q.map (pullbackTensorIntegralBraiding l E X A B).hom)
          (Q.map (pullbackTensorIntegralBraiding l E X A' B').hom) := by
      subst A' B'
      rfl
    have he' : HEq ((pullbackTensorRationalBraiding l E X (F.obj M) (F.obj N)).hom)
        (Q.map ((pullbackTensorIntegralBraiding l E X (I.obj M.obj) (I.obj N.obj)).hom)) :=
      he.trans (hsym hm hn)
    have hright := heq_comp
      (by rw [hF, hTY]; rfl)
      (by rw [hTX, hF, hF]; rfl)
      (by rw [hTX, hF, hF]; rfl) hd he'
    apply eq_of_heq
    refine hleft.trans ?_
    refine (heq_of_eq (Q.map_comp _ _).symm).trans ?_
    rw [canonicalIntegralPullbackTensor_braiding_spec l E f M.obj N.obj]
    exact (heq_of_eq (Q.map_comp _ _)).trans hright.symm

/-- Coherence for the canonical commonstage comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonBraiding l _
      Ω _ _ _ Y hY) M N).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorCommonBraiding l _ Ω _ _ _ X hX)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom

end RationalCoherenceElaboration

private theorem reducedBraiding_natural
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D) [Q.Faithful]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (b : T ⋙ Q ≅ (Q.prod Q) ⋙ S)
    (β : ∀ A B, S.obj (A, B) ⟶ S.obj (B, A))
    (hβ : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      S.map (Prod.mkHom f g) ≫ β A' B' = β A B ≫ S.map (Prod.mkHom g f))
    (bi : ∀ A B, T.obj (A, B) ⟶ T.obj (B, A))
    (hb : ∀ A B, Q.map (bi A B) ≫ b.hom.app (B, A) =
      b.hom.app (A, B) ≫ β (Q.obj A) (Q.obj B))
    (M M' N N' : C) (f : M ⟶ M') (g : N ⟶ N') :
    T.map (Prod.mkHom f g) ≫ bi M' N' = bi M N ≫ T.map (Prod.mkHom g f) := by
  have hn := b.hom.naturality (Prod.mkHom f g)
  have hn' := b.hom.naturality (Prod.mkHom g f)
  change Q.map (T.map (Prod.mkHom f g)) ≫ b.hom.app (M', N') =
    b.hom.app (M, N) ≫ S.map (Prod.mkHom (Q.map f) (Q.map g)) at hn
  change Q.map (T.map (Prod.mkHom g f)) ≫ b.hom.app (N', M') =
    b.hom.app (N, M) ≫ S.map (Prod.mkHom (Q.map g) (Q.map f)) at hn'
  apply Q.map_injective
  apply (cancel_mono (b.hom.app (N', M'))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [hβ, hn']
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ S.map (Prod.mkHom (Q.map g) (Q.map f))) (hb M N).symm

private theorem representative_braiding
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (β : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (γ : ∀ P Q, S.obj (P, Q) ≅ S.obj (Q, P))
    (μ : ∀ M N, F.obj (T.obj (M, N)) ≅ S.obj (F.obj M, F.obj N))
    (hc : ∀ M N, F.map (β M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (γ (F.obj M) (F.obj N)).hom)
    (hn : ∀ P P' Q Q' (f : P ⟶ P') (g : Q ⟶ Q'),
      S.map (Prod.mkHom f g) ≫ (γ P' Q').hom =
        (γ P Q).hom ≫ S.map (Prod.mkHom g f))
    (M N : C) {A B : C} {U V P Q X Y : D}
    (a : A ≅ T.obj (M, N)) (b : B ≅ T.obj (N, M))
    (u : U ≅ F.obj A) (v : V ≅ F.obj B)
    (p : P ≅ F.obj M) (q : Q ≅ F.obj N)
    (x : X ≅ S.obj (P, Q)) (y : Y ≅ S.obj (Q, P)) :
    (u.hom ≫ F.map (a.hom ≫ (β M N).hom ≫ b.inv) ≫ v.inv) ≫
      (v.hom ≫ F.map b.hom ≫ (μ N M).hom ≫
        S.map (Prod.mkHom q.inv p.inv) ≫ y.inv) =
    (u.hom ≫ F.map a.hom ≫ (μ M N).hom ≫
      S.map (Prod.mkHom p.inv q.inv) ≫ x.inv) ≫
      (x.hom ≫ (γ P Q).hom ≫ y.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% (hc M N), ← reassoc_of% (hn _ _ _ _ p.inv q.inv)]

private theorem localizedBraiding_natural
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (T : A × A ⥤ A) (bi : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (bi M' N').hom =
        (bi M N).hom ≫ T.map (Prod.mkHom g f))
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (br : ∀ M N, F.obj (M, N) ≅ F.obj (N, M))
    (ho : ∀ MN, F.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩)
    (hm : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a b' : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
          ((a * b') ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (hb : ∀ M N, HEq (br M N).hom
      ((ScalarLocalization.localization R A p).map (bi M.obj N.obj).hom)) :
    ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      F.map (Prod.mkHom f g) ≫ (br M' N').hom =
        (br M N).hom ≫ F.map (Prod.mkHom g f) := by
  intro M M' N N' f g
  obtain ⟨b, he, hp⟩ := hm M M' N N'
  obtain ⟨b', he', hp'⟩ := hm N N' M M'
  rw [he, he']
  have ht (a : Localization.Away p) (f : M.obj ⟶ M'.obj)
      (c : Localization.Away p) (g : N.obj ⟶ N'.obj) :
      b (a ⊗ₜ[R] f) (c ⊗ₜ[R] g) ≫ (br M' N').hom =
        (br M N).hom ≫ b' (c ⊗ₜ[R] g) (a ⊗ₜ[R] f) := by
    have hl := heq_comp (ho (M, N)) (ho (M', N')) (ho (N', M'))
      (hp f g a c) (hb M' N')
    have hr := heq_comp (ho (M, N)) (ho (N, M)) (ho (N', M'))
      (hb M N) (hp' g f c a)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R A p _ _ _
        (1 ⊗ₜ[R] (bi M'.obj N'.obj).hom)
        ((a * c) ⊗ₜ[R] T.map (Prod.mkHom f g)) =
      ScalarLocalization.composition R A p _ _ _
        ((c * a) ⊗ₜ[R] T.map (Prod.mkHom g f))
        (1 ⊗ₜ[R] (bi M.obj N.obj).hom)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one, mul_comm c a, hn]
  induction f using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, Limits.zero_comp,
      Limits.comp_zero]
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, Limits.zero_comp,
        Limits.comp_zero]
    | tmul c g => exact ht a f c g
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add, hg, hg']
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add, hf, hf']


attribute [local irreducible] pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  rationalDerivedTensor rationalDerivedPullback canonicalRationalPullbackTensor


private theorem integralBraiding_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfIntegralConstructibleCategory l E W)
    (f : M ⟶ M') (g : N ⟶ N') :
    (constructibleIntegralTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorIntegralBraiding l E W M' N').hom =
      (pullbackTensorIntegralBraiding l E W M N).hom ≫
        (constructibleIntegralTensor l E W).map (Prod.mkHom g f) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let Q := coherentReduction l E W
    let T := constructibleIntegralTensor l E W
    let S := (pullbackTensorCalculus l E W).systemClosed.tensor
    let b := reduction_tensor l E W
    let β := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      (pullbackTensorCalculus l E W).systemClosed
      (pullbackTensorCalculus l E W).systemTensorModel
    have hb (A B) : Q.map (pullbackTensorIntegralBraiding l E W A B).hom ≫
        b.hom.app (B, A) = b.hom.app (A, B) ≫ β.hom.app (Q.obj A, Q.obj B) :=
      by
        unfold pullbackTensorIntegralBraiding
        exact (pullbackTensorIntegralBraiding_existsUnique l E W A B).exists.choose_spec
    have := (coherentReduction_fullyFaithful l E W).2
    exact reducedBraiding_natural Q T S b (fun A B ↦ β.hom.app (A, B))
      (fun _ _ _ _ a b ↦ β.hom.naturality (Prod.mkHom a b))
      (fun A B ↦ (pullbackTensorIntegralBraiding l E W A B).hom) hb M M' N N' f g



attribute [local irreducible] sfIntegralConstructible

private theorem rationalBraiding_natural (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfRationalConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N') :
    (rationalDerivedTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorRationalBraiding l E W M' N').hom =
      (pullbackTensorRationalBraiding l E W M N).hom ≫
        (rationalDerivedTensor l E W).map (Prod.mkHom g f) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    exact localizedBraiding_natural
      (R := Padic.coefficientExtensionIntegers l E)
      (A := sfIntegralConstructibleCategory l E W) _ (constructibleIntegralTensor l E W)
      (pullbackTensorIntegralBraiding l E W) (integralBraiding_natural l E W)
      (rationalDerivedTensor l E W) (pullbackTensorRationalBraiding l E W)
      (by
        unfold rationalDerivedTensor
        exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1)
      (by
        unfold rationalDerivedTensor
        exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2)
      (by
        intro M N
        unfold pullbackTensorRationalBraiding
        exact (pullbackTensorRationalBraiding_existsUnique l E W M N).exists.choose_spec)
      M M' N N' f g

-- Keep cached category data while comparing representatives over one coefficient field.
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

/-- The normalized commonstage comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalCommonStagePullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalCommonStagePullbackTensor_braiding l _ Ω _ _ _ X Y f hX hY) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    intro M N
    let F := commonStageDerivedPullback l Ω f
    let OY := commonStageTensorObject l Ω Y
    let OX := commonStageTensorObject l Ω X
    let P := commonStagePullbackObject l Ω f
    have hoY (A B) : (commonStageDerivedTensor l Ω Y).obj (A, B) = OY A B := by
      unfold commonStageDerivedTensor
      exact (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 A B
    have hoX (A B) : (commonStageDerivedTensor l Ω X).obj (A, B) = OX A B := by
      unfold commonStageDerivedTensor
      exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 A B
    have hoF (A) : F.obj A = P A := by
      dsimp only [F]
      unfold commonStageDerivedPullback
      exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A
    obtain ⟨L₁, hMN, hNM⟩ := exists_ge_ge (OY M N).stage (OY N M).stage
    obtain ⟨L₂, h₁, hPMN⟩ := exists_ge_ge L₁ (OX (P M) (P N)).stage
    obtain ⟨L, h₂, hPNM⟩ := exists_ge_ge L₂ (OX (P N) (P M)).stage
    have hMN := hMN.trans (h₁.trans h₂)
    have hNM := hNM.trans (h₁.trans h₂)
    have hPMN := hPMN.trans h₂
    have hM : M.stage ≤ L :=
      ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans hMN
    have hN : N.stage ≤ L :=
      ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans hMN
    have hmap {A B A' B' : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
        (hA : A = A') (hB : B = B')
        (hA' : A'.stage ≤ L) (hB' : B'.stage ≤ L)
        (a : A ⟶ B) (b : A'.toStage hA' ⟶ B'.toStage hB')
        (hab : HEq a (ofHom A' B' L hA' hB' b)) :
        HEq (F.map a) (ofHom (P A') (P B') L hA' hB'
          ((commonStagePullbackComparison l Ω f A' L hA').hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map b ≫
            (commonStagePullbackComparison l Ω f B' L hB').inv)) := by
      subst A B
      cases hab
      dsimp only [F, P]
      unfold commonStageDerivedPullback
      exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
        A' B' L hA' hB' b
    have hβ := (pullbackTensorCommonBraiding_existsUnique l Ω Y M N).exists.choose_spec
      L hMN hNM
    change HEq (pullbackTensorCommonBraiding l Ω Y M N).hom _ at hβ
    have hβmap := hmap (hoY M N) (hoY N M) hMN hNM
      (pullbackTensorCommonBraiding l Ω Y M N).hom _ hβ
    have hμ := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M N).exists.choose_spec
      L hMN
    have hμ' := (canonicalCommonStagePullbackTensor_existsUnique l Ω f N M).exists.choose_spec
      L hNM
    change HEq (canonicalCommonStagePullbackTensor l Ω f M N).hom _ at hμ
    change HEq (canonicalCommonStagePullbackTensor l Ω f N M).hom _ at hμ'
    have hβX := (pullbackTensorCommonBraiding_existsUnique l Ω X (P M) (P N)).exists.choose_spec
      L hPMN hPNM
    change HEq (pullbackTensorCommonBraiding l Ω X (P M) (P N)).hom _ at hβX
    have hβeq : HEq (pullbackTensorCommonBraiding l Ω X (F.obj M) (F.obj N)).hom
        (pullbackTensorCommonBraiding l Ω X (P M) (P N)).hom := by
      rw [hoF M, hoF N]
    have hl := heq_comp
      (by rw [hoY, hoF]) (by rw [hoY, hoF])
      (by rw [hoX, hoF, hoF]) hβmap hμ'
    have hr := heq_comp
      (by rw [hoY, hoF]) (by rw [hoX, hoF, hoF])
      (by rw [hoX, hoF, hoF]) hμ (hβeq.trans hβX)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _ =
      ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _
    refine (StageSystem.PairCategory.mkHom_comp_mkHom _ _).trans
      ((congrArg (ofHom _ _ L _ _) ?_).trans
        (StageSystem.PairCategory.mkHom_comp_mkHom _ _).symm)
    exact @representative_braiding (Stage l Ω Y L) (Stage l Ω X L)
        (stageCategory l Ω Y L) (stageCategory l Ω X L)
        (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y)
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
        (pullbackTensorRationalBraiding l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y)
        (pullbackTensorRationalBraiding l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
        (canonicalRationalPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (canonicalRationalPullbackTensor_braiding_spec l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
        (rationalBraiding_natural l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
        (M.toStage hM) (N.toStage hN) _ _ _ _ _ _ _ _
        (commonStageTensorComparison l Ω Y M N L hMN)
        (commonStageTensorComparison l Ω Y N M L hNM)
        (commonStagePullbackComparison l Ω f (OY M N) L hMN)
        (commonStagePullbackComparison l Ω f (OY N M) L hNM)
        (commonStagePullbackComparison l Ω f M L hM)
        (commonStagePullbackComparison l Ω f N L hN)
        (commonStageTensorComparison l Ω X (P M) (P N) L hPMN)
        (commonStageTensorComparison l Ω X (P N) (P M) L hPNM)

end HigherCoherence

-- Avoid unfolding completed interfaces while checking the assembly statement.
attribute [local irreducible]
  canonicalCommonStagePullbackTensor
  pullbackTensorIntegralComposition pullbackTensorRationalComposition
  pullbackTensorCommonComposition canonicalIntegralPullbackTensor_composition
  canonicalRationalPullbackTensor_composition canonicalCommonStagePullbackTensor_composition
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  canonicalIntegralPullbackTensor_reduction pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  pullbackTensorCommonLeft pullbackTensorCommonRight pullbackTensorCommonAssociator
  pullbackTensorCommonBraiding pullbackTensorIntegralUnit pullbackTensorIntegralUnitReduction
  pullbackTensorRationalUnit pullbackTensorIntegralLeftUnitor pullbackTensorRationalLeftUnitor
  pullbackTensorIntegralRightUnitor pullbackTensorRationalRightUnitor
  pullbackTensorRationalScalarUnit pullbackTensorCommonUnit pullbackTensorCommonUnitStage
  pullbackTensorCommonLeftUnitor pullbackTensorCommonRightUnitor
  canonicalIntegralPullbackTensor_unit canonicalRationalPullbackTensor_unit
  canonicalCommonStagePullbackTensor_unit canonicalIntegralPullbackTensor_associative
  canonicalRationalPullbackTensor_associative canonicalCommonStagePullbackTensor_associative
  canonicalIntegralPullbackTensor_braiding canonicalRationalPullbackTensor_braiding
  canonicalCommonStagePullbackTensor_braiding


/-- The canonical derived pullback/tensor comparison exists at every coefficient
level and is natural in both inputs.  At finite level this is the comparison for
the constant-coefficient morphism of ringed pro-etale topoi.  At integral level it
is the inverse-limit comparison on completed reductions; at rational level it is
its scalar localization; and at algebraically closed level it is the common-stage
comparison over a finite coefficient compositum.  The comparison is compatible
with the tensor unit, associativity, signed symmetry, coefficient reduction and
scalar extension, and with composition of pullbacks, as in the proof steps of
`lem-pur-derived-pullback-tensor-iso`.

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4 (Tag 07A4,
label `lemma-pullback-tensor-product`), for the morphism of ringed topoi
(X_proet, (A_{E,n})_X) -> (Y_proet, (A_{E,n})_Y); the integral, rational and Qlbar
levels follow the level-by-level definitions of the operations in
def-weil-derived-pullback-tensor-hom.

Proof plan (the node's numbered steps):

1. At finite level choose compatible small representatives of the pro-etale sites as in [def-weil-
   proetale-inverse-image]. The inverse image and its constant-ring map make $f_n$ a morphism of
   ringed topoi. By [prop-weil-pbc-proetale-constant-exact], module pullback is exact and agrees
   with inverse image with the coefficient action transported through
   $f^{-1}(A_{E,n})_Y\cong(A_{E,n})_X$. Thus its derived functor is precisely the finite operation
   in [def-weil-derived-pullback-tensor-hom]. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-
   pullback] with $R=(A_{E,n})_Y$ and $S=(A_{E,n})_X$. Its displayed isomorphism, natural in both
   arguments, is $\mu_{f;M,N}$. That theorem is unbounded, so it applies to all the finite-level
   inputs claimed here; no finite Tor dimension of $A_{E,n}$ is assumed.

2. Choose flat-term K-flat resolutions $P,Q$ by [lem-pc-kflat-resolution]. The closure assertion
   [lem-pur-kflat-total-tensor-model] shows that $\operatorname{Tot}(P\otimes Q)$ is K-flat with
   flat terms, so all iterated tensors below compute derived tensors. On these models the
   comparison is totalized from the module map of [lem-weil-pbc-ringed-topoi-module-pullback-
   tensor], with the signed differential from [def-pc-tensor-complex-sheaves].

3. Use the chain maps of [lem-pur-cochain-pullback-tensor-coherence]. Their pure-tensor formula
   and inverse are the ordinary comparison of [lem-weil-pbc-ringed-topoi-module-pullback-tensor],
   and the chain lemma supplies associativity, signed symmetry, units, composition and
   coefficient-change equations. By [lem-weil-pbc-site-derived-tensor-descent] these maps and
   equations descend from the K-flat resolving class to arbitrary finite-level derived inputs.

4. For integral $M,N$, choose flat-term K-flat representatives $P,Q$ by [lem-pc-kflat-resolution].
   Set $P_n=P\otimes_{R_Y}B_{Y,n}$ and $Q_n=Q\otimes_{R_Y}B_{Y,n}$, with actual quotient
   transitions. Put $T_n=\operatorname{Tot}(P_n\otimes Q_n)$, $U_n=f_n^*P_n$, $V_n=f_n^*Q_n$, and
   $W_n=\operatorname{Tot}(U_n\otimes V_n)$. The quotient and pullback models are flat-term K-flat
   by [lem-pur-kflat-change-of-rings, lem-weil-pbc-ringed-pullback-preserves-kflat], and the
   tensor totals by step 2. The normalization and coherent reduction assertions of [lem-pur-
   completed-operation-tower-substitution] and [lem-coef-normalized-dvr-effectivity] identify
   these systems with the reductions of the completed operations in [def-pur-integral-derived-
   operations]. Here $B_{Y,n}=(A_{E,n})_Y$ and $R_Y=\varprojlim B_{Y,n}$, as in the normalized
   tower convention [def-coef-normalized-dvr-tower].

5. The cochain maps of [lem-pur-cochain-pullback-tensor-coherence] give the strict tower
   isomorphism $f_n^*T_n\to W_n$ and its strict inverse. Apply [lem-pur-integral-tower-limit-
   comparison] to the $T,U,V$ of step 4. With the substitution identifications of [lem-pur-
   completed-operation-tower-substitution], its actual derived-limit map is the required
   comparison between completed pullback of $M\widehat\otimes^L N$ and completed tensor of
   $Lf^*M,Lf^*N$. The functor is [lem-weil-pbc-ringed-strict-tower-homotopy-limit]; its naturality
   and the resolution comparisons of [lem-pur-integral-operations-well-defined] give naturality in
   $M,N$ and independence of the chosen representatives.

6. By [lem-pur-integral-operations-preserve-constructible], $M\widehat\otimes^L N$ is
   constructible on $Y$ and its pullback is constructible on $X$. The same lemma first puts
   $Lf^*M,Lf^*N$ in $D^b_c(X,\mathcal O_E)$ and then puts their completed tensor there. This is a
   full subcategory of the ambient derived category [def-weil-derived-complete-integral-detailed],
   so the ambient comparison and its inverse are morphisms of that subcategory.

7. The finite associativity, signed symmetry, unit and pullback-composition equations from [lem-
   pur-cochain-pullback-tensor-coherence] are compatible with every quotient transition. The
   tower-level assertion [lem-pur-integral-coherence-tower] therefore identifies them as
   equalities of strict normalized systems and gives their integral images after applying [lem-
   pur-completed-operation-tower-substitution] and [lem-weil-pbc-ringed-strict-tower-homotopy-
   limit].

8. The coherent counit comparisons of [lem-coef-normalized-dvr-effectivity], applied to the source
   and target systems of the strict comparison, identify its reduction with the finite comparison.
   Their naturality applies to this actual map of systems, and [lem-pur-completed-operation-tower-
   substitution] carries the counits to the completed operations. No faithfulness assertion for
   individual finite-reduction functors is needed.

9. For $E\subset L$ put $B_m=\mathcal O_L/\varpi_L^m$. The strict quotient models of [def-weil-
   integral-scalar-extension] and the coherent reduction model [lem-pur-coefficient-extension-
   reduction-model] give the normalized $B_\bullet$-tower, including ramified extensions. The
   quotient K-flatness is [lem-pur-kflat-change-of-rings], and the scalar-association and
   transition equations are exactly [lem-pur-scalar-extension-tower-coherence].

10. Use the pullback and tensor scalar-extension isomorphisms of [lem-pur-integral-operations-
   scalar-extension] in their canonical quotient-model form. The tower coherence statement [lem-
   pur-scalar-extension-tower-coherence] says that both routes around the comparison square send
   $b\otimes(x\otimes y)$ to $(b\otimes x)\otimes(1\otimes y)$ and commute with every quotient and
   coefficient square. Applying [lem-weil-pbc-ringed-strict-tower-homotopy-limit] and [lem-pur-
   completed-operation-tower-substitution] gives the integral scalar-extension square.

11. By [def-weil-rationalization-karoubi], every rational object is an integral object and every
   morphism is a finite sum of $u\otimes a$, with $u$ integral and $a\in E$. Define $\mu^E$ to be
   the image $\mu^{\mathcal O_E}\otimes1$; its inverse is the image of the integral inverse. The
   operations on rational morphisms are the scalar extensions specified in [def-weil-derived-
   pullback-tensor-hom]. The integral naturality identity for $u,v$, multiplied by the
   corresponding scalars, gives rational naturality; add the resulting identities for sums. Every
   integral coherence equation remains an equality after tensoring Hom groups with $E$, so the
   rational associativity, symmetry, unit and composition equations follow. The scalar-extension
   square of the preceding scalar-extension steps likewise remains commutative, since the rational
   scalar-extension functor is the one induced from the integral scalar-extension functor.

12. For objects $(E,M),(E',N)$ at the algebraically closed level, choose a common finite
   coefficient field $L$ and form the rational comparison there, conjugated by the scalar-
   extension comparisons as prescribed in [def-weil-derived-pullback-tensor-hom]. Represent the
   inverse by the inverse rational comparison with the inverse conjugating comparisons. In [def-
   weil-algebraically-closed-coefficients], morphisms are classes over common finite fields, and
   two representatives agree if they agree after passage to a further common field. The scalar-
   extension calculation after rationalization says precisely that passing from $L$ to any larger
   field sends this comparison to the same comparison there; hence the class and its inverse are
   independent of $L$. Represent any finite naturality or coherence diagram over a single common
   finite field; the rational identity proved in the preceding rationalization step gives its
   equality in the colimit Hom group. This proves all the asserted compatibilities at $\Qlb$,
   including scalar extension into $\Qlb$.
(blueprint: lem-pur-derived-pullback-tensor-iso) -/
theorem derivedPullbackTensorIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
      [IsAlgClosure (Padic l) Ω] :
    ((∃ eF : (finiteIntrinsicDerivedTensor l E Y n) ⋙ (finiteDerivedPullback l E n f) ≅
        ((finiteDerivedPullback l E n f).prod (finiteDerivedPullback l E n f)) ⋙
          (finiteIntrinsicDerivedTensor l E X n),
        ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
          eF.app (M,N) = (@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N) ∧
      (@canonicalFinitePullbackTensor_associativity_condition l _ E _ _ _ X Y f n hX hY) ∧
      (@canonicalFinitePullbackTensor_unit_condition l _ E _ _ _ X Y f n hX hY) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)],
        (@canonicalFinitePullbackTensor_composition_condition l _ E _ _ _ X Y Z f h n hX hY hZ)) ∧
      (@canonicalFinitePullbackTensor_braiding_condition l _ E _ _ _ X Y f n hX hY) ∧
      (∃ eI : (@constructibleIntegralTensor l _ E _ _ _ Y hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ X Y f hX hY) ≅
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY).prod
          (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)) ⋙ (@constructibleIntegralTensor
          l _ E _ _ _ X hX),
        ∀ (M N : sfIntegralConstructibleCategory l E Y),
          eI.app (M,N) = (@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N) ∧
      (∃ eR : (@rationalDerivedTensor l _ E _ _ _ Y hY) ⋙ (@rationalDerivedPullback l _ E _ _ _ X Y
        f hX hY) ≅
        ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY).prod (@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)) ⋙ (@rationalDerivedTensor l _ E _ _ _ X hX),
        ∀ (M N : sfRationalConstructibleCategory l E Y),
          eR.app (M,N) = (@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N) ∧
      (∃ eC : (@commonStageDerivedTensor l _ Ω _ _ _ Y hY) ⋙ (@commonStageDerivedPullback l _ Ω _ _
        _ X Y f hX hY) ≅
        ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY).prod (@commonStageDerivedPullback l _
          Ω _ _ _ X Y f hX hY)) ⋙ (@commonStageDerivedTensor l _ Ω _ _ _ X hX),
        ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
          eC.app (M,N) = (@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N) ∧
      (∀ M N : sfRationalConstructibleCategory l E Y,
        HEq ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom
          ((sfRationalConstructibleLocalization l E X).map
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj).hom)) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : sfIntegralConstructibleCategory l E Y),
        (@canonicalIntegralPullbackTensor_composition l _ E _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : sfRationalConstructibleCategory l E Y),
        (@canonicalRationalPullbackTensor_composition l _ E _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
        (@canonicalCommonStagePullbackTensor_composition l _ Ω _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ M N, (@canonicalIntegralPullbackTensor_reduction l _ E _ _ _ X Y f hX hY) M N) ∧
      (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_associative l _ Ω _ _ _ X Y f hX hY) ∧
      (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_braiding l _ Ω _ _ _ X Y f hX hY) ∧
      (@canonicalIntegralPullbackTensor_unit l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_unit l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_unit l _ Ω _ _ _ X Y f hX hY) ∧
      (∀ {m q : ℕ} (hq : q ≤ m)
        (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
        (canonicalFinitePullbackTensor_quotient_condition l E f (hX := hX) (hY := hY)
          (m := m) (n := q) hq M N)) ∧
      (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
        (M N : sfIntegralConstructibleCategory l E Y),
        (canonicalIntegralPullbackTensor_scalar_condition l E L ι f
          (hX := hX) (hY := hY) M N)) ∧
      (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
        (M N : sfRationalConstructibleCategory l E Y),
        (canonicalRationalPullbackTensor_scalar_condition l E L ι f
          (hX := hX) (hY := hY) M N)) ∧
      (∀ (n : ℕ) (M N : coefficientSequenceDerived l E Y),
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
          ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
            ((pullbackTensorSequenceDerived l E f).obj M,
              (pullbackTensorSequenceDerived l E f).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom ((pullbackTensorDerivedEvaluation l E f n).hom.app M)
              ((pullbackTensorDerivedEvaluation l E f n).hom.app N)) =
        (pullbackTensorDerivedEvaluation l E f n).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
          (finiteDerivedPullback l E n f).map
            (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
          ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
            ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
            ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom)) := by
  sorry

end WeilConjectures
