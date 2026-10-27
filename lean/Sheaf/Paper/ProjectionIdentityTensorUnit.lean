/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y7
-/
module

public import Sheaf.Paper.FinitePartialPullbackTensor
public import Sheaf.Paper.CommonProjectionPullbackTensorCompatibility
import Sheaf.Paper.FinitePartialTensorIdentityComposition
import Sheaf.Paper.HigherTensorIdentityComposition

/-! # Tensor compatibility of the normalized identity pullback

Source: the identity paragraph of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem normalized_identity_naturality
    {A : Type*} [Category* A] (U : A ⥤ A) (e : U ≅ 𝟭 A) (M : A) :
    U.map (e.hom.app M) = e.hom.app (U.obj M) := by
  apply (cancel_mono (e.hom.app M)).1
  exact e.hom.naturality (e.hom.app M)

private theorem tensor_identity_of_composition
    {A B : Type*} [Category* A] [Category* B]
    (T : A × B ⥤ A) (U : A ⥤ A) (V : B ⥤ B)
    (μ : T ⋙ U ≅ U.prod V ⋙ T)
    (c : ∀ M, U.obj M ≅ U.obj (U.obj M))
    (d : ∀ L, V.obj L ≅ V.obj (V.obj L))
    (hc : ∀ M L, μ.hom.app (M, L) ≫
        T.map (Prod.mkHom ((c M).hom) ((d L).hom)) =
      (c (T.obj (M, L))).hom ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, V.obj L))
    (e : U ≅ 𝟭 A) (f : V ≅ 𝟭 B)
    (he : ∀ M, (c M).hom ≫ e.hom.app (U.obj M) = 𝟙 (U.obj M))
    (hf : ∀ L, (d L).hom ≫ f.hom.app (V.obj L) = 𝟙 (V.obj L))
    (M : A) (L : B) :
    μ.hom.app (M, L) ≫ T.map (Prod.mkHom (e.hom.app M) (f.hom.app L)) =
      e.hom.app (T.obj (M, L)) := by
  let ν := μ.hom.app (M, L) ≫ T.map (Prod.mkHom (e.hom.app M) (f.hom.app L))
  have hn := μ.hom.naturality (Prod.mkHom (e.hom.app M) (f.hom.app L))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [normalized_identity_naturality U e M, normalized_identity_naturality V f L] at hn
  have h := congrArg (fun k ↦ k ≫
    T.map (Prod.mkHom (e.hom.app (U.obj M)) (f.hom.app (V.obj L)))) (hc M L)
  have h' : μ.hom.app (M, L) =
      (c (T.obj (M, L))).hom ≫ U.map ν ≫ μ.hom.app (M, L) := by
    have h'' : μ.hom.app (M, L) ≫ T.map (𝟙 (U.obj M, V.obj L)) =
        (c (T.obj (M, L))).hom ≫ U.map ν ≫ μ.hom.app (M, L) := by
      simpa only [ν, Category.assoc, ← T.map_comp, prod_comp, he, hf,
        ← prod_id, ← hn, U.map_comp, Functor.id_obj] using h
    rw [T.map_id (U.obj M, V.obj L)] at h''
    exact (Category.comp_id (μ.hom.app (M, L))).symm.trans h''
  have hν : U.map ν = e.hom.app (U.obj (T.obj (M, L))) := by
    apply (cancel_epi ((c (T.obj (M, L))).hom)).1
    rw [he]
    exact ((cancel_mono (μ.hom.app (M, L))).1 (by
      simpa only [Category.id_comp, Category.assoc] using h')).symm
  have hnν := e.hom.naturality ν
  dsimp only [Functor.id_map] at hnν
  rw [hν] at hnν
  exact ((cancel_epi (e.hom.app (U.obj (T.obj (M, L))))).1 hnν).symm

private def uncurry_tensor_comparison
    {A B : Type*} [Category* A] [Category* B]
    (T : A ⥤ B ⥤ A) (U : A ⥤ A) (V : B ⥤ B)
    (μ : (Functor.postcompose₂.obj U).obj T ≅
      (((Functor.whiskeringLeft₂ A).obj U).obj V).obj T) :
    Functor.uncurry.obj T ⋙ U ≅ U.prod V ⋙ Functor.uncurry.obj T :=
  NatIso.ofComponents (fun p ↦ (μ.app p.1).app p.2) (by
    rintro ⟨M, L⟩ ⟨M', L'⟩ ⟨a, b⟩
    have h := (Functor.uncurry.mapIso μ).hom.naturality (Prod.mkHom a b)
    change (U.map ((T.map a).app L) ≫ U.map ((T.obj M').map b)) ≫
        (μ.hom.app M').app L' =
      (μ.hom.app M).app L ≫
        ((T.map (U.map a)).app (V.obj L) ≫ (T.obj (U.obj M')).map (V.map b)) at h
    simpa only [Functor.uncurry_obj_map, Functor.comp_map, Functor.prod_map,
      Functor.map_comp, Category.assoc, Iso.app_hom, Functor.prod_obj] using h)

private theorem fullSubcategory_eqToHom
    {A : Type*} [Category* A] {P : ObjectProperty A}
    {K L : P.FullSubcategory} (h : K = L) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  cases h
  rfl

private theorem compositor_normalization
    {A : Type*} [Category* A] {F : A ⥤ A} (e : F ≅ 𝟭 A)
    {K : A} (K' : A) (h : K = F.obj K')
    (c : K ≅ F.obj (F.obj K'))
    (hc : c.hom ≫ e.hom.app (F.obj K') = eqToHom h) :
    (eqToIso h.symm ≪≫ c).hom ≫ e.hom.app (F.obj K') = 𝟙 (F.obj K') := by
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, hc, eqToHom_trans,
    eqToHom_refl]

/-- The normalized pullback identity respects the specified tensor comparisons at all
four coefficient stages. This assertion involves inverse image and tensor only.
Source: prop-sf-pf-coherence.proof.md, identity sentence; the composition equations
of lem-pur-derived-pullback-tensor-iso
(blueprint: lem-sf-projection-identity-tensor-unit).
Proof: the canonical identity inverse-image comparison respects tensor on ordinary
module sheaves, as both routes send a pure tensor to that same tensor. Derive the
comparison on K-flat representatives. At finite coefficients conjugate by the
specified coefficient equivalence, cancel its units, and restrict the second
variable through the full finite-Tor inclusion. This gives precisely
pullbackTensorComparison. At integral coefficients prove the same equation on
coherent quotient systems before reconstruction, retaining the actual completion
unit. Naturality with respect to every quotient transition permits reconstruction
of this equation. Rationalization preserves the equation, and common-stage
inclusion preserves it after choosing a common finite coefficient field for the
objects and arrows. The specified pullback compositors preserve these units by
their normalization (finitePullCompositionNormalization, integral reduction and
coefficient-comparison pullComposition). Finally any e in the statement equals
the canonical identity comparison: cancel the invertible compositor to obtain
equality on pulled-back objects; apply naturality to the canonical unit component
and cancel its invertible pullback to obtain equality on every object. Substitute
that equality in the canonical tensor-unit equation. This uses no Tor bound on
the first variable, no direct-image adjunction, and no projection map. It covers
zero objects, the empty scheme, and n = 1 without modification. -/
theorem projectionIdentity_tensorUnit (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∀ (e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X)),
      (∀ M : sixFunctorFiniteCategory D C E n hn X,
        (S.finite.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
            e.hom.app ((S.finite.pull (𝟙 X)).obj M) =
          eqToHom (congrArg (fun f ↦ (S.finite.pull f).obj M)
            (Category.id_comp (𝟙 X)))) →
      ∀ (M : sixFunctorFiniteCategory D C E n hn X)
        (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
        (CompactSupportFiniteProjection.pullbackTensorComparison
          S.toSixFunctorFiniteOperations (𝟙 X) M L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).map
              (e.hom.app M)).app
              ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations (𝟙 X)).obj
                L) ≫
            ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              M).map (ObjectProperty.isoMk
              (finiteTorConstructible C.l E n hn X.obj.left)
              (X := (CompactSupportFiniteProjection.torPull
                S.toSixFunctorFiniteOperations (𝟙 X)).obj L) (Y := L)
              ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
                (e.app ⟨L.obj, L.property.1⟩))).hom =
          e.hom.app
            (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              M).obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∀ (e : S.higher.integral.pull (𝟙 X) ≅ 𝟭 (sfIntegralConstructibleCategory C.l E X.obj.left)),
      (∀ M : sfIntegralConstructibleCategory C.l E X.obj.left,
        (S.higher.integral.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
            e.hom.app ((S.higher.integral.pull (𝟙 X)).obj M) =
          eqToHom (congrArg (fun f ↦ (S.higher.integral.pull f).obj M)
            (Category.id_comp (𝟙 X)))) →
      ∀ (M L : sfIntegralConstructibleCategory C.l E X.obj.left),
        ((projectionPullbackTensor (S.higher.integralExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L ≫
            ((S.higher.integralTensor X).map (e.hom.app M)).app
              ((S.higher.integral.pull (𝟙 X)).obj L) ≫
            ((S.higher.integralTensor X).obj M).map (e.hom.app L) =
          e.hom.app (((S.higher.integralTensor X).obj M).obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∀ (e : S.higher.rational.pull (𝟙 X) ≅ 𝟭 (sfRationalConstructibleCategory C.l E X.obj.left)),
      (∀ M : sfRationalConstructibleCategory C.l E X.obj.left,
        (S.higher.rational.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
            e.hom.app ((S.higher.rational.pull (𝟙 X)).obj M) =
          eqToHom (congrArg (fun f ↦ (S.higher.rational.pull f).obj M)
            (Category.id_comp (𝟙 X)))) →
      ∀ (M L : sfRationalConstructibleCategory C.l E X.obj.left),
        ((projectionPullbackTensor (S.higher.rationalExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L ≫
            ((S.higher.rationalTensor X).map (e.hom.app M)).app
              ((S.higher.rational.pull (𝟙 X)).obj L) ≫
            ((S.higher.rationalTensor X).obj M).map (e.hom.app L) =
          e.hom.app (((S.higher.rationalTensor X).obj M).obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      ∀ (e : S.closure.commonStage.pull (𝟙 X) ≅ 𝟭 (generalAlgebraicallyClosedConstructibleCategory
        C.l C.Qbar X.obj.left)),
      (∀ M : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
        (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
            e.hom.app ((S.closure.commonStage.pull (𝟙 X)).obj M) =
          eqToHom (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj M)
            (Category.id_comp (𝟙 X)))) →
      ∀ (M L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
        ((projectionPullbackTensor (S.closure.commonStageExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L ≫
            ((S.closure.commonStageTensor X).map (e.hom.app M)).app
              ((S.closure.commonStage.pull (𝟙 X)).obj L) ≫
            ((S.closure.commonStageTensor X).obj M).map (e.hom.app L) =
          e.hom.app (((S.closure.commonStageTensor X).obj M).obj L)) := by
  constructor
  · intro X
    let : IsProper (𝟙 X : X ⟶ X).hom.left := by
      change IsProper (𝟙 X.obj.left)
      infer_instance
    intro e he M L
    let S₀ := S.toSixFunctorFiniteOperations
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S₀ (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S₀ X)
    let c := fun K ↦
      eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj K)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        (S.finite.pullComposition (𝟙 X) (𝟙 X)).app K
    let d := fun K ↦
      eqToIso (congrArg (fun f ↦ (CompactSupportFiniteProjection.torPull S₀ f).obj K)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        CompactSupportFiniteProjection.torPullComposition S₀ (𝟙 X) (𝟙 X) K
    obtain ⟨μ, hμ, hc⟩ := finitePartialTensor_identityComposition S₀ X
    let f : V ≅ 𝟭 (finiteTorConstructibleCategory C.l E n hn X.obj.left) :=
      NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
        ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
          (e.app ⟨K.obj, K.property.1⟩))) (by
        intro K K' a
        apply ObjectProperty.hom_ext
        let b : (⟨K.obj, K.property.1⟩ : sixFunctorFiniteCategory D C E n hn X) ⟶
            ⟨K'.obj, K'.property.1⟩ := ObjectProperty.homMk a.hom
        exact congrArg (fun k ↦ k.hom) (e.hom.naturality b))
    have hec : ∀ K, (c K).hom ≫ e.hom.app (U.obj K) = 𝟙 (U.obj K) := by
      intro K
      exact compositor_normalization e K _ _ (he K)
    have hfd : ∀ K, (d K).hom ≫ f.hom.app (V.obj K) = 𝟙 (V.obj K) := by
      intro K
      apply ObjectProperty.hom_ext
      have h := congrArg (fun k ↦ k.hom) (hec ⟨K.obj, K.property.1⟩)
      simpa only [d, c, f, U, V, S₀, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
        ObjectProperty.isoMk_hom,
        Functor.mapIso_hom, NatIso.ofComponents_hom_app, ObjectProperty.homMk_hom,
        ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
        CompactSupportFiniteProjection.torPullComposition, fullSubcategory_eqToHom,
        ObjectProperty.ι_map, CompactSupportFiniteProjection.torPull,
        ObjectProperty.lift, ObjectProperty.ιOfLE, Functor.comp_obj,
        ObjectProperty.ι, inducedFunctor_obj, inducedFunctor_map, Functor.id_obj] using h
    have h := tensor_identity_of_composition T U V μ c d hc e f hec hfd M L
    rw [show μ.hom.app (M, L) =
      (CompactSupportFiniteProjection.pullbackTensorComparison S₀ (𝟙 X) M L).hom from
        congrArg Iso.hom (hμ M L)] at h
    exact h
  · constructor
    · intro X
      let : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      intro e he M L
      let U := S.higher.integral.pull (𝟙 X)
      let T := S.higher.integralTensor X
      let μ := projectionPullbackTensor (S.higher.integralExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X)))
      let c := fun K ↦
        eqToIso (congrArg (fun f ↦ (S.higher.integral.pull f).obj K)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.higher.integral.pullComposition (𝟙 X) (𝟙 X)).app K
      have hec : ∀ K, (c K).hom ≫ e.hom.app (U.obj K) = 𝟙 (U.obj K) := by
        intro K
        exact compositor_normalization e K _ _ (he K)
      exact tensor_identity_of_composition (Functor.uncurry.obj T) U U
        (uncurry_tensor_comparison T U U μ) c c
        ((higherTensor_identityComposition S).1 X) e e hec hec M L
    · constructor
      · intro X
        let : IsProper (𝟙 X : X ⟶ X).hom.left := by
          change IsProper (𝟙 X.obj.left)
          infer_instance
        intro e he M L
        let U := S.higher.rational.pull (𝟙 X)
        let T := S.higher.rationalTensor X
        let μ := projectionPullbackTensor (S.higher.rationalExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))
        let c := fun K ↦
          eqToIso (congrArg (fun f ↦ (S.higher.rational.pull f).obj K)
            (Category.id_comp (𝟙 X)).symm) ≪≫
            (S.higher.rational.pullComposition (𝟙 X) (𝟙 X)).app K
        have hec : ∀ K, (c K).hom ≫ e.hom.app (U.obj K) = 𝟙 (U.obj K) := by
          intro K
          exact compositor_normalization e K _ _ (he K)
        exact tensor_identity_of_composition (Functor.uncurry.obj T) U U
          (uncurry_tensor_comparison T U U μ) c c
          ((higherTensor_identityComposition S).2.1 X) e e hec hec M L
      · intro X
        let : IsProper (𝟙 X : X ⟶ X).hom.left := by
          change IsProper (𝟙 X.obj.left)
          infer_instance
        intro e he M L
        let U := S.closure.commonStage.pull (𝟙 X)
        let T := S.closure.commonStageTensor X
        let μ := projectionPullbackTensor (S.closure.commonStageExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))
        let c := fun K ↦
          eqToIso (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj K)
            (Category.id_comp (𝟙 X)).symm) ≪≫
            (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X)).app K
        have hec : ∀ K, (c K).hom ≫ e.hom.app (U.obj K) = 𝟙 (U.obj K) := by
          intro K
          exact compositor_normalization e K _ _ (he K)
        exact tensor_identity_of_composition (Functor.uncurry.obj T) U U
          (uncurry_tensor_comparison T U U μ) c c
          ((higherTensor_identityComposition S).2.2 X) e e hec hec M L


end WeilConjectures
