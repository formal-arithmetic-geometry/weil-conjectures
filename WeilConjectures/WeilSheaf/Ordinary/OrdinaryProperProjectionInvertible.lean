/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons
import WeilConjectures.WeilSheaf.SixFunctors.CommonProperProjectionFiniteModel
import WeilConjectures.SixFunctors.Rational.RationalProperProjectionInvertible
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackTensorNaturality
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality

/-! # Ordinary proper projection formula

Source: BS 6.8.14--6.8.15; Stacks 070I, 08BJ, 07A4 and 0G7E.
(blueprint: lem-sf-ordinary-proper-projection-invertible).

The formula concerns ordinary continuous-coefficient modules, with no Weil structure.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  WeilConjectures.geometricCommonStageDirectImage
  WeilConjectures.geometricCommonStageAdjunction
  WeilConjectures.rationalDerivedPullback WeilConjectures.rationalDerivedTensor
  WeilConjectures.canonicalRationalPullbackTensor
  WeilConjectures.canonicalCommonStagePullbackTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

-- Cache the source and target of the mate before specializing its categories.
@[irreducible] private def projectionMate
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (phi : ∀ P Q, F.obj (T.obj (P, Q)) ⟶ U.obj (F.obj P, F.obj Q))
    (E : B) (Q : A) : T.obj (R.obj E, Q) ⟶ R.obj (U.obj (E, F.obj Q)) :=
  adj.homEquiv _ _ (phi (R.obj E) Q ≫
    U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))

-- Tensor-mate coherence needs naturality of the two realization tensors, but
-- only the components of the pullback/tensor comparison.
private theorem projection_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : ∀ P Q, F.obj (T.obj (P, Q)) ⟶ U.obj (F.obj P, F.obj Q))
    (tG : T ⋙ G ⟶ (G.prod G) ⋙ V)
    (tH : U ⋙ H ⟶ (H.prod H) ⋙ W) (tK : V ⋙ K ⟶ (K.prod K) ⋙ W)
    (a : F ⋙ H ≅ G ⋙ K) (b : R ⋙ G ≅ H ⋙ S)
    (hc : ∀ P Q : A,
      H.map (tF P Q) ≫ tH.app (F.obj P, F.obj Q) ≫
        W.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
      a.hom.app (T.obj (P, Q)) ≫ K.map (tG.app (P, Q)) ≫
        tK.app (G.obj P, G.obj Q))
    (hb : ∀ E, H.map (adj.counit.app E) =
      a.hom.app (R.obj E) ≫ K.map (b.hom.app E) ≫ adj'.counit.app (H.obj E))
    (E : B) (Q : A) :
    G.map (adj.homEquiv _ _ (tF (R.obj E) Q ≫
        U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)))) ≫
      b.hom.app (U.obj (E, F.obj Q)) ≫
      S.map (tH.app (E, F.obj Q) ≫
        W.map (Prod.mkHom (𝟙 _) (a.hom.app Q))) =
    tG.app (R.obj E, Q) ≫
      V.map (Prod.mkHom (b.hom.app E) (𝟙 _)) ≫
      adj'.homEquiv _ _ (tK.app (S.obj (H.obj E), G.obj Q) ≫
        W.map (Prod.mkHom (adj'.counit.app (H.obj E)) (𝟙 _))) := by
  have hex (E : B) : K.map (b.hom.app E) ≫ adj'.counit.app (H.obj E) =
      a.inv.app (R.obj E) ≫ H.map (adj.counit.app E) := by
    rw [hb]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have ht (P Q : A) :
      a.inv.app (T.obj (P, Q)) ≫ H.map (tF P Q) ≫
        tH.app (F.obj P, F.obj Q) =
      K.map (tG.app (P, Q)) ≫ tK.app (G.obj P, G.obj Q) ≫
        W.map (Prod.mkHom (a.inv.app P) (a.inv.app Q)) := by
    apply (cancel_epi (a.hom.app (T.obj (P, Q)))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    have h := congrArg
      (fun f ↦ f ≫ W.map (Prod.mkHom (a.inv.app P) (a.inv.app Q))) (hc P Q)
    simp only [Category.assoc, ← W.map_comp, prod_comp, Prod.mkHom,
      Iso.hom_inv_id_app] at h
    change H.map (tF P Q) ≫ tH.app (F.obj P, F.obj Q) ≫
      W.map (𝟙 (H.obj (F.obj P), H.obj (F.obj Q))) =
        a.hom.app (T.obj (P, Q)) ≫ K.map (tG.app (P, Q)) ≫
          tK.app (G.obj P, G.obj Q) ≫
            W.map (Prod.mkHom (a.inv.app P) (a.inv.app Q)) at h
    have hid : W.map (𝟙 (H.obj (F.obj P), H.obj (F.obj Q))) = 𝟙 _ :=
      W.map_id (H.obj (F.obj P), H.obj (F.obj Q))
    rw [hid] at h
    have hcid : tH.app (F.obj P, F.obj Q) ≫
        𝟙 (W.obj (H.obj (F.obj P), H.obj (F.obj Q))) =
        tH.app (F.obj P, F.obj Q) := Category.comp_id _
    rw [hcid] at h
    simpa only [Category.assoc] using h
  let pi := adj.homEquiv _ _ (tF (R.obj E) Q ≫
    U.map (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))
  apply (adj'.homEquiv _ _).symm.injective
  change (adj'.homEquiv _ _).symm (G.map pi ≫ b.hom.app _ ≫ S.map _) = _
  rw [adj'.homEquiv_naturality_left_symm, adj'.homEquiv_naturality_right_symm]
  rw [adj'.homEquiv_counit, hex]
  dsimp only [Functor.id_obj, Functor.comp_obj] at *
  simp only [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hn := a.inv.naturality pi
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  simp only [← Category.assoc]
  rw [hn]
  have hpi : F.map pi ≫ adj.counit.app (U.obj (E, F.obj Q)) =
      tF (R.obj E) Q ≫ U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)) :=
    (adj.homEquiv _ _).symm_apply_apply _
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hpi, H.map_comp, Category.assoc]
  have htH := tH.naturality (Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))
  have htK := tK.naturality (Prod.mkHom (b.hom.app E) (𝟙 (G.obj Q)))
  dsimp only [Functor.comp_map, Functor.prod_map] at htH htK
  rw [reassoc_of% htH, reassoc_of% htK, reassoc_of% (ht (R.obj E) Q)]
  simp only [← W.map_comp]
  congr 2
  congr 1
  ext
  · simpa using (hex E).symm
  · simp

-- Reverse a tensor square along its three comparison isomorphisms.
private theorem inverse_tensor_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D}
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : ∀ P Q, F.obj (T.obj (P, Q)) ⟶ U.obj (F.obj P, F.obj Q))
    (tG : (G.prod G) ⋙ V ≅ T ⋙ G)
    (tH : (H.prod H) ⋙ W ≅ U ⋙ H)
    (tK : V ⋙ K ⟶ (K.prod K) ⋙ W) (a : F ⋙ H ≅ G ⋙ K)
    (hc : ∀ P Q, K.map (tG.hom.app (P, Q)) ≫ a.inv.app (T.obj (P, Q)) ≫
      H.map (tF P Q) = tK.app (G.obj P, G.obj Q) ≫
        W.map (Prod.mkHom (a.inv.app P) (a.inv.app Q)) ≫
        tH.hom.app (F.obj P, F.obj Q)) (P Q : A) :
    H.map (tF P Q) ≫ tH.inv.app (F.obj P, F.obj Q) ≫
        W.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
      a.hom.app (T.obj (P, Q)) ≫ K.map (tG.inv.app (P, Q)) ≫
        tK.app (G.obj P, G.obj Q) := by
  apply (cancel_epi (K.map (tG.hom.app (P, Q)) ≫ a.inv.app _)).1
  simp only [Category.assoc]
  rw [reassoc_of% (hc P Q)]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← W.map_comp, prod_comp, Prod.mkHom, Iso.inv_hom_id_app]
  rw [← K.map_comp_assoc, Iso.hom_inv_id_app, K.map_id, Category.id_comp]
  change tK.app (G.obj P, G.obj Q) ≫
    W.map (𝟙 (K.obj (G.obj P), K.obj (G.obj Q))) = tK.app (G.obj P, G.obj Q)
  have hid : W.map (𝟙 (K.obj (G.obj P), K.obj (G.obj Q))) = 𝟙 _ :=
    W.map_id (K.obj (G.obj P), K.obj (G.obj Q))
  rw [hid]
  exact Category.comp_id (tK.app (G.obj P, G.obj Q))

-- Naturality of a counit mate for an arbitrary pair of tensor bifunctors.
private theorem projection_naturality
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (mu : T ⋙ F ⟶ F.prod F ⋙ U)
    {E E' : B} {P P' : A} (e : E ⟶ E') (q : P ⟶ P') :
    T.map (Prod.mkHom (R.map e) q) ≫
        adj.homEquiv _ _ (mu.app (R.obj E', P') ≫
          U.map (Prod.mkHom (adj.counit.app E') (𝟙 _))) =
      adj.homEquiv _ _ (mu.app (R.obj E, P) ≫
          U.map (Prod.mkHom (adj.counit.app E) (𝟙 _))) ≫
        R.map (U.map (Prod.mkHom e (F.map q))) := by
  apply adj.homEquiv_naturality_left_square
  have ht := mu.naturality (Prod.mkHom (R.map e) q)
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  rw [← Category.assoc, ht]
  simp only [Category.assoc, ← U.map_comp]
  congr 2
  ext
  · exact adj.counit.naturality e
  · simp

-- Cancel the projection comparison in abstract categories, before specializing
-- to the large concrete sheaf-category models.
private theorem projection_isIso_of_comparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : ∀ P Q, F.obj (T.obj (P, Q)) ⟶ U.obj (F.obj P, F.obj Q))
    (tG : T ⋙ G ≅ (G.prod G) ⋙ V)
    (tH : U ⋙ H ≅ (H.prod H) ⋙ W) (tK : V ⋙ K ⟶ (K.prod K) ⋙ W)
    (a : F ⋙ H ≅ G ⋙ K) (b : R ⋙ G ≅ H ⋙ S)
    (hc : ∀ P Q : A,
      H.map (tF P Q) ≫ tH.hom.app (F.obj P, F.obj Q) ≫
        W.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
      a.hom.app (T.obj (P, Q)) ≫ K.map (tG.hom.app (P, Q)) ≫
        tK.app (G.obj P, G.obj Q))
    (hb : ∀ E, H.map (adj.counit.app E) =
      a.hom.app (R.obj E) ≫ K.map (b.hom.app E) ≫ adj'.counit.app (H.obj E))
    (E : B) (Q : A)
    (hi : IsIso (projectionMate adj T U tF E Q)) :
    IsIso (projectionMate adj' V W (fun P Q ↦ tK.app (P, Q)) (H.obj E) (G.obj Q)) := by
  unfold projectionMate at hi ⊢
  have hpi : IsIso (adj.homEquiv _ _ (tF (R.obj E) Q ≫
      U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)))) := hi
  have : IsIso (Prod.mkHom (𝟙 (H.obj E)) (a.hom.app Q)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (Prod.mkHom (b.hom.app E) (𝟙 (G.obj Q))) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have hs := projection_square adj adj' T U V W tF tG.hom tH.hom tK a b hc hb E Q
  have hr : IsIso
      (G.map (adj.homEquiv _ _ (tF (R.obj E) Q ≫
          U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)))) ≫
        b.hom.app (U.obj (E, F.obj Q)) ≫
        S.map (tH.hom.app (E, F.obj Q) ≫
          W.map (Prod.mkHom (𝟙 _) (a.hom.app Q)))) := inferInstance
  rw [hs] at hr
  exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hr)

private theorem projection_isIso_of_iso
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (mu : T ⋙ F ⟶ F.prod F ⋙ U)
    {E E' : B} {P P' : A} (e : E ≅ E') (q : P ≅ P')
    (hi : IsIso (projectionMate adj T U (fun P Q ↦ mu.app (P, Q)) E P)) :
    IsIso (projectionMate adj T U (fun P Q ↦ mu.app (P, Q)) E' P') := by
  unfold projectionMate at hi ⊢
  have hpi : IsIso (adj.homEquiv _ _ (mu.app (R.obj E, P) ≫
      U.map (Prod.mkHom (adj.counit.app E) (𝟙 _)))) := hi
  have : IsIso (Prod.mkHom (R.map e.hom) q.hom) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (Prod.mkHom e.hom (F.map q.hom)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have hr : IsIso
      (adj.homEquiv _ _ (mu.app (R.obj E, P) ≫
          U.map (Prod.mkHom (adj.counit.app E) (𝟙 _))) ≫
        R.map (U.map (Prod.mkHom e.hom (F.map q.hom)))) := inferInstance
  rw [← projection_naturality adj T U mu e.hom q.hom] at hr
  exact (isIso_comp_left_iff _ _).mp hr

-- Essential-image lifting uses the image clause already carried by R.
private theorem ordinary_constructible_lift
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    (M : DerivedCategory (modules l X R)) (hM : boundedConstructible l X R M) :
    ∃ K, Nonempty ((ordinary l X R).obj K ≅ M) := by
  obtain ⟨M₀, hM₀, ⟨i⟩⟩ := hM
  obtain ⟨K, ⟨e⟩⟩ := (R.image M₀).mp hM₀
  refine ⟨K, ?_⟩
  unfold ordinary
  change Nonempty ((sectionDerived l X R).obj (R.J.obj K) ≅ M)
  exact ⟨(sectionDerived l X R).mapIso e ≪≫ i⟩

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

private def commonTensorPullbackNat
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    commonStageDerivedTensor l Ω Y ⋙ commonStageDerivedPullback l Ω f ⟶
      (commonStageDerivedPullback l Ω f).prod (commonStageDerivedPullback l Ω f) ⋙
        commonStageDerivedTensor l Ω X where
  app MN := (canonicalCommonStagePullbackTensor l Ω f MN.1 MN.2).hom
  naturality {MN MN'} h := by
    exact commonStagePullbackTensor_naturality l Ω f
      (by
        intro E _ _ _ M M' N N' a b
        exact canonicalRationalPullbackTensor_naturality l E f a b) h.1 h.2

set_option maxHeartbeats 800000 in
-- Comparing the stage representatives and counit squares exceeds the default heartbeat budget.
private theorem commonProperProjection_isIso [IsProper p]
    (hl : IsUnit (l : AlgebraicClosure k₀))
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
    (K : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    IsIso (properCommonProjection k₀ l p hl K L) := by
  let X := (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let W := (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let f := NativeBaseChange.geometricMap k₀ p
  have : IsProper f :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) p
      (comp_over p (Spec (CommRingCat.of k₀))) inferInstance
  let E := Padic.finiteCoefficientCompositum l (PadicAlgCl l) K.stage L.stage
  have hK : K.stage ≤ E :=
    ((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1 K.stage L.stage).1
  have hL : L.stage ≤ E :=
    ((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1 K.stage L.stage).2
  let F := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let IX : sfRationalConstructibleCategory l F X ⥤
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X :=
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let IY : sfRationalConstructibleCategory l F W ⥤
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) W :=
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := W) E
  let P : sfRationalConstructibleCategory l F X := K.toStage hK
  let Q : sfRationalConstructibleCategory l F W := L.toStage hL
  let adjC := geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) hl f
  let TX := commonStageDerivedTensor l (PadicAlgCl l) X
  let TY := commonStageDerivedTensor l (PadicAlgCl l) W
  obtain ⟨G, adj, tX, tY, a, b, ht, hc⟩ :=
    properCommonProjection_finiteStageComparison k₀ l p hl E
  let mu := commonTensorPullbackNat l (PadicAlgCl l) f
  have hi := rationalProperProjection_isIso l F (AlgebraicClosure k₀) hl f G adj P Q
  have hi' : IsIso (projectionMate adj (rationalDerivedTensor l F W)
      (rationalDerivedTensor l F X)
      (fun P Q ↦ (canonicalRationalPullbackTensor l F f P Q).hom) P Q) := by
    simpa only [projectionMate, rationalProperProjection] using hi
  have himage := projection_isIso_of_comparison (G := IY) (H := IX) adj adjC
    (rationalDerivedTensor l F W) (rationalDerivedTensor l F X) TY TX
    (fun P Q ↦ (canonicalRationalPullbackTensor l F f P Q).hom)
    tY.symm tX.symm mu a b ht hc P Q hi'
  let eK : IX.obj P ≅ K :=
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage K hK).symm
  let eL : IY.obj Q ≅ L :=
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) W).isoToStage L hL).symm
  have hresult := projection_isIso_of_iso
    (F := commonStageDerivedPullback l (PadicAlgCl l) f)
    (R := properCommonPush k₀ l p hl) adjC TY TX mu
    (E := IX.obj P) (E' := K) (P := IY.obj Q) (P' := L) eK eL himage
  simpa only [projectionMate, mu, commonTensorPullbackNat, properCommonProjection] using hresult

set_option maxHeartbeats 800000 in
-- Comparing the stage representatives and counit squares exceeds the default heartbeat budget.
/-- The ordinary counit projection mate is invertible on bounded constructible
continuous-coefficient complexes.
Source: Step 6 and the invertibility assertion of Step 7 of
lem-sf-native-proper-projection-realization; blueprint latest,
fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection;
BS 6.8.14--6.8.15
(blueprint: lem-sf-ordinary-proper-projection-invertible).

Proof: by the exact essential-image clause of the locally finite realization,
lift the two bounded constructible complexes to the common-stage category.
The section-derived presentation carries the lifting isomorphisms to the ordinary
module category. Each common-stage object has a finite coefficient-field model;
take the compositum so both objects have models over the same field. Over this
field bounded constructibility is the finite-Tor domain. Apply the rational
projection formula to integral representatives and extend to their finite cones,
shifts and rationalized arrows, then pass to their common-stage classes.
Use the compactification (identity,p). The identity extension by zero and its
tensor comparison are identity maps under the unit comparison, so its projection
arrow is exactly the counit mate properCommonProjection. It is therefore invertible.
The tensor, unit and counit equations in the supplied proper comparison identify
the ordinary image of this arrow with properOrdinaryProjection, conjugated by
the specified tensor, pull and push isomorphisms. The ordinary realization
preserves its inverse. Naturality of the counit mate transports invertibility
along the two lifting isomorphisms to the original complexes. This uses finite
Tor amplitude only over a field; it imposes no additional hypothesis on either
bounded constructible complex. The same argument includes zero objects and
empty schemes; no faithful forgetting of derived Weil morphisms is used. -/
theorem properOrdinaryProjection_isIso [IsProper p]
    (R : LocallyFiniteAdicRealization.Realization l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (S : LocallyFiniteAdicRealization.Realization l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
    (A : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R)
    (B : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)
    (hl : IsUnit (l : AlgebraicClosure k₀))
    (C : Proper.Comparison l (NativeBaseChange.geometricMap k₀ p) R S
      (AlgebraicClosure k₀) hl A B)
    (M : DerivedCategory (modules l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R))
    (N : DerivedCategory (modules l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S))
    (hM : boundedConstructible l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R M)
    (hN : boundedConstructible l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S N) :
    IsIso (properOrdinaryProjection k₀ l p R S A B C.operations C.tensor M N) := by
  obtain ⟨K, ⟨eM⟩⟩ := ordinary_constructible_lift l _ R M hM
  obtain ⟨L, ⟨eN⟩⟩ := ordinary_constructible_lift l _ S N hN
  let X := (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let W := (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let f := NativeBaseChange.geometricMap k₀ p
  let UX := ordinary l X R
  let UY := ordinary l W S
  let FB := ContinuousRational.derivedPull f C.operations.coefficient
  let RB := ContinuousRational.DirectImage.derivedPush f C.operations.coefficient
  have hcommon := commonProperProjection_isIso k₀ l p hl K L
  have hcommonTensor (P Q : generalAlgebraicallyClosedConstructibleCategory l
      (PadicAlgCl l) W) :
      UX.map (canonicalCommonStagePullbackTensor l (PadicAlgCl l) f P Q).hom ≫
        A.tensor.inv.app
          ((commonStageDerivedPullback l (PadicAlgCl l) f).obj P,
           (commonStageDerivedPullback l (PadicAlgCl l) f).obj Q) ≫
        A.closed.tensor.map (Prod.mkHom (C.a.hom.app P) (C.a.hom.app Q)) =
      C.a.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) W).obj (P, Q)) ≫
        FB.map (B.tensor.inv.app (P, Q)) ≫
        C.tensor.tensor.hom.app (UY.obj P, UY.obj Q) := by
    exact inverse_tensor_square
      (F := commonStageDerivedPullback l (PadicAlgCl l) f)
      (G := UY) (H := UX) (K := FB)
      (commonStageDerivedTensor l (PadicAlgCl l) W)
      (commonStageDerivedTensor l (PadicAlgCl l) X) B.closed.tensor A.closed.tensor
      (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l) f P Q).hom)
      B.tensor A.tensor C.tensor.tensor.hom C.a C.tensor_compatibility P Q
  have hcommon' : IsIso (projectionMate
      (geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) hl f)
      (commonStageDerivedTensor l (PadicAlgCl l) W)
      (commonStageDerivedTensor l (PadicAlgCl l) X)
      (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l) f P Q).hom) K L) := by
    unfold projectionMate
    exact hcommon
  have honimage := projection_isIso_of_comparison (G := UY) (H := UX)
    (geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) hl f)
    C.operations.adjunction
    (commonStageDerivedTensor l (PadicAlgCl l) W)
    (commonStageDerivedTensor l (PadicAlgCl l) X)
    B.closed.tensor A.closed.tensor
    (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l) f P Q).hom)
    B.tensor.symm A.tensor.symm C.tensor.tensor.hom
    C.a C.b hcommonTensor C.counit K L hcommon'
  have hresult := projection_isIso_of_iso (F := FB) (R := RB) C.operations.adjunction
    B.closed.tensor A.closed.tensor C.tensor.tensor.hom
    (E := UX.obj K) (E' := M) (P := UY.obj L) (P' := N) eM eN honimage
  simpa only [projectionMate, properOrdinaryProjection] using hresult

end AlgebraicGeometry.ProEtaleWeilSheaf
