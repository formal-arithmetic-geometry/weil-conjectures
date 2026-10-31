/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilChosenDualityExchangeData
import WeilConjectures.AlgebraicGeometry.WeilChosenExchangeConstruction
import WeilConjectures.AlgebraicGeometry.WeilChosenTransposeNaturality

/-! # Specified Weil exchange for chosen dualizing objects

Source: cor-coef-verdier-weil-equivariance.proof.md, evaluation and adjunction paragraphs;
thm-sf-verdier-exchange.proof.md, Steps 1--3; lem-sf-tensor-hom.proof.md, Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange).
The existing interfaces are re-exported unchanged from WeilChosenDualityExchangeData.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c va vb vc
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
namespace WeilConjectures.WeilChosenDualityExchange
open PodConstructibleMate

private def exchange_of_natural
    {X : Type a} {Y : Type b} [Category.{va} X] [Category.{vb} Y]
    {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}
    (exceptional : F ⊣ G) (ordinary : P ⊣ Q)
    (TX : X ⥤ X ⥤ X) (TY : Y ⥤ Y ⥤ Y)
    (HX : Xᵒᵖ × X ⥤ X) (HY : Yᵒᵖ × Y ⥤ Y)
    (closedX : ∀ M, TX.obj M ⊣ (Functor.curry.obj HX).obj (op M))
    (closedY : ∀ N, TY.obj N ⊣ (Functor.curry.obj HY).obj (op N))
    (projection : ∀ M A, (TY.obj (F.obj M)).obj A ≅
      F.obj ((TX.obj M).obj (P.obj A))) (omegaX : X) (omegaY : Y)
    (comparison : G.obj omegaY ≅ omegaX)
    (hn : ∀ {M N : Xᵒᵖ} (v : M ⟶ N),
      (F.op ⋙ (Functor.curry.obj HY).flip.obj omegaY).map v ≫
          transposeComponent exceptional ordinary TX TY HX HY closedX closedY
            projection omegaY N.unop =
        transposeComponent exceptional ordinary TX TY HX HY closedX closedY
            projection omegaY M.unop ≫
          ((Functor.curry.obj HX).flip.obj (G.obj omegaY) ⋙ Q).map v) :
    Exchange exceptional ordinary TX TY HX HY closedX closedY projection
      omegaX omegaY comparison := by
  let tau : F.op ⋙ (Functor.curry.obj HY).flip.obj omegaY ⟶
      (Functor.curry.obj HX).flip.obj (G.obj omegaY) ⋙ Q :=
    { app M := transposeComponent exceptional ordinary TX TY HX HY closedX closedY
        projection omegaY M.unop
      naturality _ _ v := hn v }
  let substitution := Functor.whiskerRight ((Functor.curry.obj HX).flip.map comparison.hom) Q
  exact
    { tau := tau
      tau_app := fun _ ↦ rfl
      exchange := tau ≫ substitution
      exchange_app := fun _ ↦ rfl }

section Geometric
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
variable (A : SixFunctorCommonStages D C) (W : CommonLifts D C A.commonStage)
variable (X Y : Models D) (f : X ⟶ Y)

private theorem ordinary_maps : OrdinaryMaps D C A W X Y f := by
  unfold OrdinaryMaps ordinaryAdjunction CommonLifts.pullFunctor CommonLifts.directFunctor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K
    rfl
  · intro M
    rfl
  · intro K M v v₀ hv
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    cases hv
    rfl
  · intro K M w w₀ hw
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    cases hw
    rfl

/-- Specified Weil exchange data for arbitrary chosen structure right adjoints.
All operation parameters are the recorded operation datum and its standard lifts;
no ambient exceptional-adjoint datum, perfectness, or preservation hypothesis is added.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md;
thm-sf-verdier-exchange.proof.md Step 1 and lem-sf-tensor-hom.proof.md Steps 1--2
(blueprint: lem-sf-weil-chosen-duality-exchange).

Proof, following the seven DAG steps:
1. Integral constructible internal Hom closes the Hom domains on separated finite-type
schemes. Pullback, completed tensor and compact support preserve constructibility;
rationalization and the common-stage formulas give the asserted bounded categories.
The canonical exceptional adjoints already have these constructible codomains.
2. Frobenius pullback monoidal-adjunction coherence identifies the direct-image exchange
as the mate of the inverse pullback comparison. The lifted ordinary adjunction therefore
has precisely the original unit, counit and the forward and inverse Hom bijections.
3. Apply rightAdjointUniq to the chosen and canonical structure adjunctions. Its counit
identity fixes n_X and n_Y. Mate the specified compact-support composition under the
canonical constructible adjunctions. At the coefficient unit, conjugating this mate by
G(n_Y) and n_X inverse gives exactly chosenComparison, an isomorphism of pairs.
4. The evaluation-defined automorphism-Hom comparison preserves tensor-Hom transpose.
Transpose the Weil equation for evaluation; cancellation of the first structure's
isomorphism gives precisely the standard inverse-first-input Hom structure. The same
calculation backwards restricts the inverse Hom bijection. Thus HomLift uses the
original closed adjunction, also for arbitrary chosen dualizing objects.
5. Field coefficients have the whole constructible finite-Tor domain. The specified
projection formula gives projection and its carrier normalization. Compose its inverse
with evaluation, then apply the exceptional, tensor-Hom and ordinary Hom bijections.
This is transposeComponent, and every intermediate object and arrow is in its pair category.
6. For u:M→N, evaluation dinaturality and projection naturality identify the two maps
before transposition. Naturality of each of the three Hom bijections then gives
contravariant naturality of tau; these are the same restricted bijections on pairs.
7. Apply the Hom bifunctor in its second variable to chosenComparison, then apply the
ordinary direct image and compose with tau. Bifunctoriality and step 6 give naturality
of e, with exactly exchange_app. This uses no inverse of tau or e. -/
theorem weil_chosen_duality_exchange
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (S : SixFunctorOperationDatum D C E 1 (Nat.le_refl 1))
    (W : CommonLifts D C S.closure.commonStage)
    (X Y : Models D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cy : Compactification (structureMap D Y).hom.left)
    (cx : Compactification (f ≫ structureMap D Y).hom.left) :
    ∃ d : Data D C S.closure W X Y f cf cy cx, d.Laws := by
  obtain ⟨d⟩ := weil_chosen_exchange_construction D C E S W X Y f cf cy cx
  refine ⟨d, ordinary_maps D C S.closure W X Y f, ?_⟩
  intro JX JY adjX adjY
  exact ⟨exchange_of_natural _ _ _ _ _ _ _ _ _ _ _ _
    (weil_chosen_transpose_naturality D C E S W X Y f cf cy cx d
      (JY.obj d.unit.pair))⟩

end Geometric
end WeilConjectures.WeilChosenDualityExchange
