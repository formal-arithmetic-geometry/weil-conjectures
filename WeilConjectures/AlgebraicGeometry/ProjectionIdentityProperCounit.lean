/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.ProjectionIdentityTensorUnit
import WeilConjectures.AlgebraicGeometry.FiniteProperProjectionTranspose

/-! # Proper counit projection for identity

Source: the identity paragraph of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

attribute [local irreducible] CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.properComponent
  CompactSupportFiniteProjection.pullbackTensorComparison

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem counit_identity {A : Type*} [Category A] {F G : A ⥤ A}
    (adj : F ⊣ G) (e : F ≅ 𝟭 A) (M : A) :
    e.hom.app (G.obj M) ≫
        ((adj.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app M =
      adj.counit.app M := by
  have h := (adj.ofNatIsoLeft e).rightAdjointUniq_hom_app_counit Adjunction.id M
  simpa using congrArg (fun k ↦ e.hom.app (G.obj M) ≫ k) h

private theorem identity_projection {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ A} (adj : F ⊣ G) (T : A ⥤ B ⥤ A) (e : F ≅ 𝟭 A)
    (K : A) (L P : B) (t : P ⟶ L)
    (μ : F.obj ((T.obj (G.obj K)).obj L) ⟶ (T.obj (F.obj (G.obj K))).obj P)
    (π : (T.obj (G.obj K)).obj L ⟶ G.obj ((T.obj K).obj P))
    (hμ : μ ≫ (T.map (e.hom.app (G.obj K))).app P ≫
      (T.obj (G.obj K)).map t = e.hom.app ((T.obj (G.obj K)).obj L))
    (hπ : F.map π ≫ adj.counit.app ((T.obj K).obj P) =
      μ ≫ (T.map (adj.counit.app K)).app P) :
    π ≫ ((adj.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app
        ((T.obj K).obj P) ≫ (T.obj K).map t =
      (T.map (((adj.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app K)).app L := by
  let d := (adj.ofNatIsoLeft e).rightAdjointUniq Adjunction.id
  apply (cancel_epi (e.hom.app ((T.obj (G.obj K)).obj L))).1
  have hn := e.hom.naturality π
  simp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  rw [← Category.assoc (e.hom.app _) _ _, counit_identity, ← Category.assoc, hπ]
  rw [← hμ]
  have hd : (T.map (adj.counit.app K)).app P =
      (T.map (e.hom.app (G.obj K))).app P ≫ (T.map (d.hom.app K)).app P := by
    rw [← NatTrans.comp_app, ← T.map_comp, counit_identity]
  rw [hd]
  simp only [Category.assoc]
  rw [(T.map (d.hom.app K)).naturality t]
  rfl

private theorem normalizedProperProjection
    {A : Type v} [Category.{w} A] {B : Type v'} [Category.{w'} B]
    {F F₀ : B ⥤ A} {G G₀ : A ⥤ B}
    {TX TX₀ : A ⥤ A ⥤ A} {TY TY₀ : B ⥤ B ⥤ B}
    (adj : F ⊣ G) (adj₀ : F₀ ⊣ G₀)
    (mu : (Functor.postcompose₂.obj F₀).obj TY₀ ≅
      (((Functor.whiskeringLeft₂ _).obj F₀).obj F₀).obj TX₀)
    (hF : F₀ = F) (hG : G₀ = G) (hX : TX₀ = TX) (hY : TY₀ = TY)
    (ha : HEq adj₀ adj) (K : A) (L : B) :
    eqToHom (by rw [hG, hY]) ≫
        ((adj₀.rightAdjointProjectionMap mu.hom).app K).app L ≫
        eqToHom (by rw [hF, hG, hX]) =
      ((adj.rightAdjointProjectionMap
        (projectionTransportTensorComparison hF hX hY mu).hom).app K).app L := by
  subst F₀ G₀ TX₀ TY₀
  cases eq_of_heq ha
  simp [projectionTransportTensorComparison]

private theorem properProjection_normalized
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : B X) (L : B Y) :
    compactSupportProperProjection A f K L =
      (((S.pullDirectAdjunction f).rightAdjointProjectionMap
        (projectionPullbackTensor (A (compactSupportProperSquare f))).hom).app K).app L := by
  unfold compactSupportProperProjection projectionPullbackTensor
  exact normalizedProperProjection (S.pullDirectAdjunction f)
      (A (compactSupportProperSquare f)).stage.properAdjunction
      (A (compactSupportProperSquare f)).stage.tensorPullback
      (A (compactSupportProperSquare f)).properPull
      (A (compactSupportProperSquare f)).properPush
      (A (compactSupportProperSquare f)).tensorBar
      (A (compactSupportProperSquare f)).tensorY
      (A (compactSupportProperSquare f)).properAdjunction K L

private theorem properProjection_identity
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (X : SixFunctorSpace D) [IsProper (𝟙 X : X ⟶ X).hom.left]
    (e : S.pull (𝟙 X) ≅ 𝟭 (B X))
    (h : ∀ M L : B X,
      ((projectionPullbackTensor (A (compactSupportProperSquare (𝟙 X)))).hom.app M).app L ≫
          ((T X).map (e.hom.app M)).app ((S.pull (𝟙 X)).obj L) ≫
          ((T X).obj M).map (e.hom.app L) = e.hom.app (((T X).obj M).obj L))
    (K L : B X) :
    compactSupportProperProjection A (𝟙 X) K L ≫
        (((S.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
          Adjunction.id).hom.app (((T X).obj K).obj ((S.pull (𝟙 X)).obj L)) ≫
        ((T X).obj K).map (e.hom.app L) =
      ((T X).map ((((S.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
        Adjunction.id).hom.app K)).app L := by
  exact identity_projection (S.pullDirectAdjunction (𝟙 X)) (T X) e K L
    ((S.pull (𝟙 X)).obj L) (e.hom.app L)
    (((projectionPullbackTensor (A (compactSupportProperSquare (𝟙 X)))).hom.app
      ((S.direct (𝟙 X)).obj K)).app L)
    (compactSupportProperProjection A (𝟙 X) K L) (h _ L) (by
      rw [properProjection_normalized]
      exact Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit
        (S.pullDirectAdjunction (𝟙 X)) _ K L)

/-- The direct-image counit projection for the identity agrees with the identity
after the normalized pullback unit and its right-adjoint mate. Compactifications
and uniqueness of the unit do not occur in this calculation.
Source: current blueprint prop-sf-pf-coherence, identity and proper-case paragraphs
(blueprint: lem-sf-projection-identity-proper-counit).
Proof: use the normalized inverse-image unit from the identity clause. Its tensor
comparison is the identity tensor comparison after this unit: termwise this is the
ordinary inverse-image tensor unit equation. The finite realization and restriction
to the finite-Tor second input preserve it. Transpose the direct-image projection
under the identity pullback/direct-image adjunction. Its transpose is the pullback
tensor comparison followed by counit tensor identity. The right-adjoint uniqueness
map d identifies that counit with the pullback identity unit. Substitute the tensor
unit equation and cancel the unit/counit pair using the adjunction triangle. The
transpose of the other side is the same map, so injectivity of transposition gives
the equation. The argument takes place on coherent systems at integral coefficients;
apply reconstruction only after the unit equation is proved. Rationalization and
common-stage inclusion preserve the counit transpose and this equation. In the
finite clause the full-subcategory inclusion is faithful, so it reflects equality.
The zero object, empty scheme, and non-finite-Tor first input are all allowed. -/
theorem projectionIdentity_properCounit (S : SixFunctorOperationDatum D C E n hn) :
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
      let d := ((S.finite.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
        Adjunction.id
      ∀ (K : sixFunctorFiniteCategory D C E n hn X) (L : finiteTorConstructibleCategory C.l E n hn
        X.obj.left),
        CompactSupportFiniteProjection.properComponent S.toSixFunctorFiniteOperations (𝟙 X) K L ≫
            d.hom.app (((CompactSupportFiniteProjection.partialTensor
              S.toSixFunctorFiniteOperations X).obj K).obj
              ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations (𝟙 X)).obj
              L)) ≫
            ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              K).map (ObjectProperty.isoMk
              (finiteTorConstructible C.l E n hn X.obj.left)
              (X := (CompactSupportFiniteProjection.torPull
                S.toSixFunctorFiniteOperations (𝟙 X)).obj L) (Y := L)
              ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
                (e.app ⟨L.obj, L.property.1⟩))).hom =
          ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).map
            (d.hom.app K)).app L) ∧
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
      let d := ((S.higher.integral.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
        Adjunction.id
      ∀ (K : sfIntegralConstructibleCategory C.l E X.obj.left) (L :
        sfIntegralConstructibleCategory C.l E X.obj.left),
        S.integralFiniteTorDomain X L →
        compactSupportProperProjection S.higher.integralExchange (𝟙 X) K L ≫
            d.hom.app (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull (𝟙 X)).obj
              L)) ≫
            ((S.higher.integralTensor X).obj K).map (e.app L).hom =
          ((S.higher.integralTensor X).map (d.hom.app K)).app L) ∧
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
      let d := ((S.higher.rational.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
        Adjunction.id
      ∀ (K : sfRationalConstructibleCategory C.l E X.obj.left) (L :
        sfRationalConstructibleCategory C.l E X.obj.left),
        compactSupportProperProjection S.higher.rationalExchange (𝟙 X) K L ≫
            d.hom.app (((S.higher.rationalTensor X).obj K).obj ((S.higher.rational.pull (𝟙 X)).obj
              L)) ≫
            ((S.higher.rationalTensor X).obj K).map (e.app L).hom =
          ((S.higher.rationalTensor X).map (d.hom.app K)).app L) ∧
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
      let d := ((S.closure.commonStage.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq
        Adjunction.id
      ∀ (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) (L :
        generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
        compactSupportProperProjection S.closure.commonStageExchange (𝟙 X) K L ≫
            d.hom.app (((S.closure.commonStageTensor X).obj K).obj ((S.closure.commonStage.pull (𝟙
              X)).obj L)) ≫
            ((S.closure.commonStageTensor X).obj K).map (e.app L).hom =
          ((S.closure.commonStageTensor X).map (d.hom.app K)).app L) := by
  have hu := projectionIdentity_tensorUnit S
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    let : IsProper (𝟙 X : X ⟶ X).hom.left := by
      change IsProper (𝟙 X.obj.left)
      infer_instance
    intro e he
    dsimp only
    intro K L
    exact identity_projection (S.finite.pullDirectAdjunction (𝟙 X))
      (CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X) e
      K L _ _ _ _ (hu.1 X e he _ L)
      (CompactSupportFiniteProjection.properComponent_transpose
        S.toSixFunctorFiniteOperations (𝟙 X) K L)
  · intro X
    let : IsProper (𝟙 X : X ⟶ X).hom.left := by
      change IsProper (𝟙 X.obj.left)
      infer_instance
    intro e he
    dsimp only
    intro K L _hL
    exact properProjection_identity S.higher.integralExchange X e (hu.2.1 X e he) K L
  · intro X
    let : IsProper (𝟙 X : X ⟶ X).hom.left := by
      change IsProper (𝟙 X.obj.left)
      infer_instance
    intro e he
    dsimp only
    intro K L
    exact properProjection_identity S.higher.rationalExchange X e (hu.2.2.1 X e he) K L
  · intro X
    let : IsProper (𝟙 X : X ⟶ X).hom.left := by
      change IsProper (𝟙 X.obj.left)
      infer_instance
    intro e he
    dsimp only
    intro K L
    exact properProjection_identity S.closure.commonStageExchange X e (hu.2.2.2 X e he) K L


end WeilConjectures
