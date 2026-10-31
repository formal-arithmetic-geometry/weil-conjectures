/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionModels
public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.AdicProperAdjunctionRealization
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicQbarConstructibleRealization

import WeilConjectures.WeilSheaf.Ordinary.OrdinaryProperProjectionInvertible

/-! # Realization of the native proper projection morphism

Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, pp. 61--62
(blueprint: lem-sf-native-proper-projection-realization).

The arrow is the actual ambient derived counit mate. Its comparisons retain their
sheaf generators, K-flat totalizations and equivariant K-injective computation.

## Main definitions

* `NativeProperProjectionRealization`: the proper projection and its compatibility squares.

## Main statements

* `native_proper_projection_realization`: existence of the normalized natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull
-- Keep the large concrete localization and cochain maps behind their stated types.
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.properSectionFactors
  AlgebraicGeometry.ProEtaleWeilSheaf.properNativePushUnit
  AlgebraicGeometry.ProEtaleWeilSheaf.properPushSheafCochain
  AlgebraicGeometry.ProEtaleWeilSheaf.properSectionCochain

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

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

set_option maxHeartbeats 800000 in
-- Elaborating the representative and adjunction squares requires more than 200000 heartbeats.
/-- All normalized comparisons for the native proper projection. These are output
data, not hypotheses on the morphism or on its constructible derived inputs.
Source: BS 6.8.14--6.8.15; native projection proof Steps 1--8
(blueprint: lem-sf-native-proper-projection-realization). -/
structure NativeProperProjectionRealization extends NativeProperProjectionModels k₀ l p where
  projection : properNativeProjectionSource k₀ l p ≅ properNativeProjectionTarget k₀ l p
  projectionMate : ∀ (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y),
    projection.hom.app (A, T) = nativeProjectionProperMate k₀ l p balanced A.obj T.obj
  projectionForget : ∀ (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y),
    (properSectionDerived k₀ l Y target).map
        (nativeProjectionProperMate k₀ l p balanced A.obj T.obj) ≫
      push.hom.app ((nativeDerivedTensor k₀ l Z).obj
        (A.obj, (nativeOpenPull k₀ l p).obj T.obj)) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
        (sourceTensor.tensor.hom.app (A.obj, (nativeOpenPull k₀ l p).obj T.obj) ≫
          sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (pull.hom.app T.obj))) =
    targetTensor.tensor.hom.app
        ((lowerStar k₀ l p).rightDerivedFunctor.obj A.obj, T.obj) ≫
      targetAt.closed.tensor.map (Prod.mkHom (push.hom.app A.obj) (𝟙 _)) ≫
      properOrdinaryProjection k₀ l p source target sourceAt targetAt
        comparison.operations comparison.tensor
        ((properSectionDerived k₀ l Z source).obj A.obj)
        ((properSectionDerived k₀ l Y target).obj T.obj)
  projectionRealization : ∀
      (K : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    (ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).map
        (properCommonProjection k₀ l p primeUnit K L) ≫
      comparison.b.hom.app
        ((commonStageDerivedTensor l (PadicAlgCl l)
          (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          (K, (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L)) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
        (sourceAt.tensor.inv.app (K,
          (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L) ≫
          sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (comparison.a.hom.app L))) =
    targetAt.tensor.inv.app ((properCommonPush k₀ l p primeUnit).obj K, L) ≫
      targetAt.closed.tensor.map (Prod.mkHom (comparison.b.hom.app K) (𝟙 _)) ≫
      properOrdinaryProjection k₀ l p source target sourceAt targetAt
        comparison.operations comparison.tensor
        ((ordinary l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source).obj K)
        ((ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).obj L)

/-- The native proper projection is a natural isomorphism on arbitrary bounded
constructible derived inputs, and its actual counit mate has the stated ordinary
and common-stage realizations, with the proper identity-open normalization.
Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection; Bhatt--Scholze 6.8.14--6.8.15, pp. 61--62
(blueprint: lem-sf-native-proper-projection-realization).

Proof:
1. The coefficient-ring comparison of lem-sf-locally-finite-coefficient-ring-realization
identifies locally finite spans and locally finite extension values: a finite basis
lies in one finite subextension. Its coefficient-map square identifies precomposition.
The native closed-forgetful theorem and the constructible realization equivalence
supply common-stage lifts of the underlying A and T. Properness and separated finite
type are preserved by geometric base change.
2. Lift the actual sheaf inverse/direct-image adjunction using
lem-sf-fixed-pair-adjunction-lift and the native Frobenius mate relation. Exact and
conservative forgetting detects exact pullback. Equivariant K-flat and K-injective
resolutions are supplied by lem-sf-weil-frobenius-action-resolutions.
3. On A to I with I equivariant K-injective, forgetting computes both pushforwards
on the same complex. Exact pullback implies pushforward preserves K-injectives by
termwise homotopy adjunction; maps into these complexes compute derived Hom by
lem-weil-pbc-kinjective-hom-derived. Thus the actual derived counit is the localized
sheaf counit followed by the inverse augmentation, on both sides. This gives
pushRepresentative and counit, using lem-sf-fixed-pair-derived-forget-comparison.
4. Balanced tensor maps send b tensor (x tensor y) to (b tensor x) tensor (1 tensor y)
and inversely multiply the two coefficients. They commute with Frobenius. Totalize
with differential d tensor 1 plus (-1)^i 1 tensor d on equivariant K-flat flat-term
resolutions. The ringed pullback K-flat theorem and conservative forgetting allow
derived descent. This gives balanced, the section tensor generators and models,
and pullTensor; use lem-sf-ringed-forget-tensor-transposition.
5. Form the actual native counit mate. The preceding counit and tensor squares
identify its forgotten composite with the ordinary projection mate of
lem-weil-pbc-ringed-projection-mate-exact. This gives projectionForget by functoriality;
faithfulness of derived forgetting is not assumed.
6. Descend A and T to a common finite coefficient field. At field stages bounded
constructible equals bounded constructible finite-Tor, so thm-sf-pf-field applies
to every T in the statement. Use compactification (identity,p) in def-exchange-projection:
the identity-open tensor comparison is the identity, leaving properCommonProjection.
7. Substitute the normalized proper-realization counit, unit and tensor equations
of lem-sf-adic-proper-adjunction-realization in that common-stage mate. This gives
projectionRealization with its actual a and b, not merely an object isomorphism.
Since realization carries the field projection isomorphism to the ordinary mate,
the latter is invertible.
8. Conservative native forgetting detects invertibility. The inverse is natural
by multiplying the naturality square by the two inverses. Native tensor closure
and pullback/direct-image preservation place source and target in the bounded
constructible full categories. Their full inclusions restrict the same arrow and
inverse. No restriction to lisse sheaves or single-degree derived objects is used.
-/
theorem native_proper_projection_realization [IsProper p] :
    Nonempty (NativeProperProjectionRealization k₀ l p) := by
  obtain ⟨M⟩ := native_proper_projection_models k₀ l p
  let := M.sourceUnits
  let := M.targetUnits
  let UX := properSectionDerived k₀ l Z M.source
  let UY := properSectionDerived k₀ l Y M.target
  let F := nativeOpenPull k₀ l p
  let FB := ContinuousRational.derivedPull
    (NativeBaseChange.geometricMap k₀ p) M.comparison.operations.coefficient
  let RB := ContinuousRational.DirectImage.derivedPush
    (NativeBaseChange.geometricMap k₀ p) M.comparison.operations.coefficient
  have hforget (A : DerivedCategory (ProEtaleWeilSheaf k₀ l Z))
      (T : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :=
    projection_square (derivedUpperStarLowerStarAdjunction k₀ l p)
      M.comparison.operations.adjunction
      (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      M.targetAt.closed.tensor M.sourceAt.closed.tensor
      (fun P Q ↦ M.balanced.mu.hom.app (P, Q))
      M.targetTensor.tensor.hom M.sourceTensor.tensor.hom M.comparison.tensor.tensor.hom
      M.pull M.push M.pullTensor M.counit A T
  have hcommonTensor (P Q : generalAlgebraicallyClosedConstructibleCategory l
      (PadicAlgCl l) (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
      (ordinary l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber M.source).map
          (canonicalCommonStagePullbackTensor l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p) P Q).hom ≫
        M.sourceAt.tensor.inv.app
          ((commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj P,
           (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj Q) ≫
        M.sourceAt.closed.tensor.map
          (Prod.mkHom (M.comparison.a.hom.app P) (M.comparison.a.hom.app Q)) =
      M.comparison.a.hom.app
          ((commonStageDerivedTensor l (PadicAlgCl l)
            (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj (P, Q)) ≫
        FB.map (M.targetAt.tensor.inv.app (P, Q)) ≫
        M.comparison.tensor.tensor.hom.app
          ((ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber M.target).obj P,
           (ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber M.target).obj Q) := by
    exact inverse_tensor_square _ _ _ _
      (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l)
        (NativeBaseChange.geometricMap k₀ p) P Q).hom)
      M.targetAt.tensor M.sourceAt.tensor M.comparison.tensor.tensor.hom
      M.comparison.a M.comparison.tensor_compatibility P Q
  have hrealization := fun K L ↦ projection_square
    (geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) M.primeUnit
      (NativeBaseChange.geometricMap k₀ p)) M.comparison.operations.adjunction
    (commonStageDerivedTensor l (PadicAlgCl l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (commonStageDerivedTensor l (PadicAlgCl l)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    M.targetAt.closed.tensor M.sourceAt.closed.tensor
    (fun P Q ↦ (canonicalCommonStagePullbackTensor l (PadicAlgCl l)
      (NativeBaseChange.geometricMap k₀ p) P Q).hom)
    M.targetAt.tensor.inv M.sourceAt.tensor.inv M.comparison.tensor.tensor.hom
    M.comparison.a M.comparison.b hcommonTensor M.comparison.counit K L
  have hbc (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
      [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
      (S : LocallyFiniteAdicRealization.Realization l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (A : WeilComplex k₀ l X) :
      boundedConstructible l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber S
        ((properSectionDerived k₀ l X S).obj A.obj) := by
    refine ⟨(nativeForget k₀ l X).obj A.obj, ?_, ⟨Iso.refl _⟩⟩
    exact (native_closed_forgetful k₀ l X).2.2.2.1 A
  have hreflect : UY.ReflectsIsomorphisms := by
    let := M.targetPresentation
    let : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.target).Additive := M.target.sectionsAdditive
    let : (nativeForget k₀ l Y).ReflectsIsomorphisms :=
      (native_closed_forgetful k₀ l Y).2.1
    change (nativeForget k₀ l Y ⋙
      (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
        M.target).mapDerivedCategory).ReflectsIsomorphisms
    infer_instance
  let := hreflect
  have hiso (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y) :
      IsIso (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj) := by
    have hOrd := properOrdinaryProjection_isIso k₀ l p M.source M.target
      M.sourceAt M.targetAt M.primeUnit M.comparison (UX.obj A.obj) (UY.obj T.obj)
      (hbc Z M.source A) (hbc Y M.target T)
    let := hOrd
    have h := hforget A.obj T.obj
    have hpairPush : IsIso (Prod.mkHom (M.push.hom.app A.obj) (𝟙 (UY.obj T.obj))) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have hpairPull : IsIso (Prod.mkHom (𝟙 (UX.obj A.obj)) (M.pull.hom.app T.obj)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have hcomp : IsIso
        (UY.map (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj) ≫
          M.push.hom.app ((nativeDerivedTensor k₀ l Z).obj (A.obj, F.obj T.obj)) ≫
          RB.map (M.sourceTensor.tensor.hom.app (A.obj, F.obj T.obj) ≫
            M.sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (M.pull.hom.app T.obj)))) := by
      rw [show UY.map (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj) ≫
          M.push.hom.app _ ≫ RB.map _ = _ from h]
      change IsIso (M.targetTensor.tensor.hom.app
          ((lowerStar k₀ l p).rightDerivedFunctor.obj A.obj, T.obj) ≫
        M.targetAt.closed.tensor.map (Prod.mkHom (M.push.hom.app A.obj) (𝟙 (UY.obj T.obj))) ≫
        properOrdinaryProjection k₀ l p M.source M.target M.sourceAt M.targetAt
          M.comparison.operations M.comparison.tensor (UX.obj A.obj) (UY.obj T.obj))
      infer_instance
    have hmapped : IsIso
        (UY.map (nativeProjectionProperMate k₀ l p M.balanced A.obj T.obj)) :=
      (isIso_comp_right_iff _ _).1 hcomp
    exact isIso_of_reflects_iso _ UY
  let := hiso
  let projection : properNativeProjectionSource k₀ l p ≅
      properNativeProjectionTarget k₀ l p :=
    NatIso.ofComponents
      (fun P ↦ asIso (nativeProjectionProperMate k₀ l p M.balanced P.1.obj P.2.obj))
      (by
        intro P Q f
        exact projection_naturality (derivedUpperStarLowerStarAdjunction k₀ l p)
          (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z) M.balanced.mu.hom
          f.1.hom f.2.hom)
  exact ⟨{
    toNativeProperProjectionModels := M
    projection := projection
    projectionMate := fun _ _ ↦ rfl
    projectionForget := fun A T ↦ hforget A.obj T.obj
    projectionRealization := hrealization }⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
