/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKunnethConstructions
import WeilConjectures.AlgebraicGeometry.RelativeProductCoefficientFactorSquares
import WeilConjectures.AlgebraicGeometry.RelativeKunnethCubeFactorTransport
import WeilConjectures.AlgebraicGeometry.RelativeKunnethClosedFibre

/-! # Relative compact-support Künneth

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
the six-factor relative map and its closed-subscheme specialization
(blueprint: thm-sf-kunneth-relative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures

private theorem index_castSucc_0 : Fin.castSucc (0 : Fin 6) = (0 : Fin 7) := rfl

private theorem index_succ_0 : Fin.succ (0 : Fin 6) = (1 : Fin 7) := rfl

private theorem index_castSucc_1 : Fin.castSucc (1 : Fin 6) = (1 : Fin 7) := rfl

private theorem index_succ_1 : Fin.succ (1 : Fin 6) = (2 : Fin 7) := rfl

private theorem index_castSucc_2 : Fin.castSucc (2 : Fin 6) = (2 : Fin 7) := rfl

private theorem index_succ_2 : Fin.succ (2 : Fin 6) = (3 : Fin 7) := rfl

private theorem index_castSucc_3 : Fin.castSucc (3 : Fin 6) = (3 : Fin 7) := rfl

private theorem index_succ_3 : Fin.succ (3 : Fin 6) = (4 : Fin 7) := rfl

private theorem index_castSucc_4 : Fin.castSucc (4 : Fin 6) = (4 : Fin 7) := rfl

private theorem index_succ_4 : Fin.succ (4 : Fin 6) = (5 : Fin 7) := rfl

private theorem index_castSucc_5 : Fin.castSucc (5 : Fin 6) = (5 : Fin 7) := rfl

private theorem index_succ_5 : Fin.succ (5 : Fin 6) = (6 : Fin 7) := rfl

private theorem heq_identity {A : Type v} [Category.{w} A] {X Y : A} (h : X = Y) :
    HEq (𝟙 X) (𝟙 Y) := by
  cases h
  rfl

private def identityAdjunctionComparison
    {A : Type v} {B : Type w} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) :
    CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison
      adj adj (𝟭 A) (𝟭 B) where
  left := Iso.refl _
  right := Iso.refl _
  unit _ := by simp
  counit _ := by simp

private def identityOperationComparison
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] (O : SixFunctorPushStage D B) :
    SixFunctorCoefficientComparison O O (fun X ↦ 𝟭 (B X)) where
  directAdjunction f := identityAdjunctionComparison (O.pullDirectAdjunction f)
  supportAdjunction f c := identityAdjunctionComparison (O.exceptionalAdjunction f c)
  openExtension _ _ := Iso.refl _
  compactification _ _ _ _ := by simp [identityAdjunctionComparison]
  openAdjunction j hj := identityAdjunctionComparison (O.openAdjunction j hj)
  openAdjunction_left _ _ := rfl
  openAdjunction_right _ _ := rfl
  composition _ _ _ _ _ _ := by simp [identityAdjunctionComparison]
  properIdentity _ _ _ := by simp [identityAdjunctionComparison]
  openIdentification _ _ _ := by simp [identityAdjunctionComparison]
  pullComposition _ _ _ := by simp [identityAdjunctionComparison]

private def identityRelativeProductComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) : RelativeProductCoefficientData R R where
  functor X := 𝟭 _
  operations := { pull := fun _ _ ↦ Iso.refl _, support := fun _ _ ↦ Iso.refl _ }
  ambientFunctor X := 𝟭 _
  ambientOperations := identityOperationComparison _
  functorNormalization _ := rfl
  pullNormalization f hf K := by
    change HEq (𝟙 _) (𝟙 _)
    have h := congrArg (fun F ↦ F.obj K) (R.coordinates.pullNormalization f hf)
    exact heq_identity h
  supportNormalization f c K := by
    change HEq (𝟙 _) (𝟙 _)
    have h := congrArg (fun F ↦ F.obj K) (R.coordinates.supportNormalization f c)
    exact heq_identity h
  tensor _ := Iso.refl _
  composition _ _ _ _ _ _ := by simp
  projection f hf c K L := by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Iso.refl_hom,
      NatTrans.id_app, Functor.prod_obj, Bifunctor.map_id, Category.comp_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id _
  exchange _ := by simp
  symmetry _ _ _ := by simp

private theorem identityRelativeProductComparison_recorded
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) :
    (identityRelativeProductComparison R).RecordedComparison := by
  apply Or.inl
  refine ⟨rfl, HEq.rfl, fun _ ↦ HEq.rfl, ?_, ?_, ?_⟩
  · intro X Y f K
    rfl
  · intro X Y f c K
    rfl
  · intro X
    apply heq_of_eq
    apply Iso.ext
    ext KL
    simp [identityRelativeProductComparison]

/-- Relative compact-support Künneth for the supplied four-stage datum, with
naturality, coefficient/proper compatibility, arbitrary geometric base change,
and the compact cohomology of ordinary closed-subscheme restrictions.

Source: current blueprint thm-sf-kunneth-relative, displayed six factors,
compatibility paragraph and final closed-subscheme display
(blueprint: thm-sf-kunneth-relative).

Proof: restrict the given operations to their finite-Tor domains, using the input
-domain lemma for every intermediate object. Full inclusion determines the
restrictions and the lifts of the supplied comparisons. The tensor is the actual
partial finite tensor, completed integral tensor, rationalized tensor or common
finite-stage tensor. A2 makes exchange invertible; A3 makes both projection
components invertible; A4 supplies the composition isomorphism. Compose those
six arrows in exactly the displayed order. Inverse naturality and tensor
bifunctoriality give naturality in both inputs. Compose the six coefficient
squares from the coefficient-factor lemma; the intermediate comparisons cancel.
For any selection of proper structural morphisms, insert the datum's specified
proper identifications at every occurrence; the proper factor equations identify
this conjugate with the direct-image projection/exchange normalization, including
the finite identity-open normalization. Compose the geometric base-change factor
squares: the endpoint on the source is exchange for h followed by monoidal
pullback of the external tensor; the endpoint on the target is monoidal pullback
followed by exchange for f and g. The exchange-pasting and tensor-pullback laws
give these specified primitive comparisons, without any assumed Künneth square.
For closed i and j over Spec k, pull back K and L by ordinary inverse image.
These restrictions remain finite Tor. Apply the same six-factor map to Z and W,
invert it, and apply the geometric-point fibre. Its canonical derived tensor
comparison identifies the tensor of fibres with the fibre of the tensor.
Pullback composition and tensor monoidality identify the exterior product on
Z × W with the ordinary restriction along i × j of K box L. The recorded
compact-sections definitions identify these three fibres with the three RΓ_c
complexes in the final formula. At finite coefficients use exact point sections;
integrally use the completed fibre; rationally localize; at algebraically closed
coefficients represent over one common finite coefficient field and realize it.
This construction includes identity maps, empty schemes and zero complexes and
makes no assertion about extraordinary cohomology with supports. -/
theorem relativeKunneth
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.Y.obj.hom] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :
    Nonempty (RelativeProductPresentation S s Q) ∧
    ∀ R : RelativeProductPresentation S s Q,
      (∀ K L, IsIso ((relativeKunnethMap R cg ch).app (K, L))) ∧
      (∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        ((relativeProductTerms Q cg ch 0).eval
          R.coordinates.operations R.coordinates.tensor).map (Prod.mkHom a b) ≫
            (relativeKunnethMap R cg ch).app (K', L') =
          (relativeKunnethMap R cg ch).app (K, L) ≫
            ((relativeProductTerms Q cg ch 6).eval
              R.coordinates.operations R.coordinates.tensor).map (Prod.mkHom a b)) ∧
      (∀ (E' : Type u) [Field E'] [Algebra (Padic C.l) E']
        [FiniteDimensional (Padic C.l) E'] (n' : ℕ) (hn' : 1 ≤ n')
        (S' : SixFunctorDatum D C E' n' hn') (s' : PodCoefficientStage)
        (R' : RelativeProductPresentation S' s' Q) (A : RelativeProductCoefficientData R R'),
        A.RecordedComparison → ∀ K L,
          (A.functor Q.Y).map ((relativeKunnethMap R cg ch).app (K, L)) ≫
              (A.objectIso cg ch 6).hom.app (K, L) =
            (A.objectIso cg ch 0).hom.app (K, L) ≫
              (relativeKunnethMap R' cg ch).app
                ((A.functor Q.X).obj K, (A.functor Q.Y').obj L)) ∧
      (Nonempty (RelativeProductProperCoordinates R.coordinates) ∧
        ∀ J : RelativeProductProperCoordinates R.coordinates,
          R.ProperNormalization J ∧
          ∀ (q : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → Bool)
            (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
              q f = true → IsProper f.hom.left) K L,
            (relativeKunnethMap R cg ch).app (K, L) ≫
                (J.objectIso q hq (relativeProductTerms Q cg ch 6)).hom.app (K, L) =
              (J.objectIso q hq (relativeProductTerms Q cg ch 0)).hom.app (K, L) ≫
                ((R.properFactors J q hq cg ch 0 ≪≫
                  R.properFactors J q hq cg ch 1 ≪≫ R.properFactors J q hq cg ch 2 ≪≫
                  R.properFactors J q hq cg ch 3 ≪≫ R.properFactors J q hq cg ch 4 ≪≫
                  R.properFactors J q hq cg ch 5).hom.app (K, L))) ∧
      (∀ (Q' : SixFunctorCompactifiedSquare D)
        [IsSeparated Q'.g.hom.left] [IsSeparated Q'.g'.hom.left]
        [IsSeparated Q'.f'.hom.left]
        (R' : RelativeProductPresentation S s Q')
        (cg' : Compactification Q'.g.hom.left)
        (ch' : Compactification (Q'.f' ≫ Q'.g).hom.left)
        (G : RelativeKunnethCube Q Q' cg ch cg' ch'),
        Nonempty (RelativeKunnethCubeComparisons R R' G) ∧
        ∀ (A : RelativeKunnethCubeComparisons R R' G) K L,
          (R'.coordinates.operations.pull G.b G.separated_b).map
              ((relativeKunnethMap R cg ch).app (K, L)) ≫ (A.targetIso K L).hom =
            (A.sourceIso K L).hom ≫
              (relativeKunnethMap R' cg' ch').app
                ((R'.coordinates.operations.pull G.x G.separated_x).obj K,
                 (R'.coordinates.operations.pull G.y G.separated_y).obj L)) ∧
      (∀ (Q' : SixFunctorCompactifiedSquare D) (J : RelativeKunnethClosedSquare Q Q'),
        relativeKunnethClosedFormula R J) := by
  refine ⟨relative_product_presentation_exists S s Q, ?_⟩
  intro R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K L
    exact inferInstanceAs (IsIso ((relativeKunnethIso R cg ch).hom.app (K, L)))
  · intro K K' L L' a b
    exact (relativeKunnethMap R cg ch).naturality (Prod.mkHom a b)
  · intro E' _ _ _ n' hn' S' s' R' A hA K L
    have h := (relative_product_coefficient_factor_squares R R' A hA cg ch).1
    have hs (i : Fin 6) : CommSq
        ((A.functor Q.Y).map ((R.factors cg ch i).hom.app (K, L)))
        ((A.objectIso cg ch i.castSucc).hom.app (K, L))
        ((A.objectIso cg ch i.succ).hom.app (K, L))
        ((R'.factors cg ch i).hom.app
          ((A.functor Q.X).obj K, (A.functor Q.Y').obj L)) := ⟨h i K L⟩
    simpa only [relativeKunnethMap, relativeKunnethIso, Iso.trans_hom,
      NatTrans.comp_app, Functor.map_comp, Category.assoc,
      index_castSucc_0, index_succ_0, index_castSucc_1, index_succ_1,
      index_castSucc_2, index_succ_2, index_castSucc_3, index_succ_3,
      index_castSucc_4, index_succ_4, index_castSucc_5, index_succ_5] using
      ((hs 0).horiz_comp ((hs 1).horiz_comp ((hs 2).horiz_comp
        ((hs 3).horiz_comp ((hs 4).horiz_comp (hs 5)))))).w
  · refine ⟨relative_product_proper_coordinates_exists R, ?_⟩
    intro J
    refine ⟨?_, ?_⟩
    · exact (relative_product_coefficient_factor_squares R R
        (identityRelativeProductComparison R)
        (identityRelativeProductComparison_recorded R) cg ch).2.2.2.2 J J |>.1
    · intro q hq K L
      simp only [relativeKunnethMap, relativeKunnethIso,
        RelativeProductPresentation.properFactors, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app,
        index_castSucc_0, index_succ_0, index_castSucc_1, index_succ_1,
        index_castSucc_2, index_succ_2, index_castSucc_3, index_succ_3,
        index_castSucc_4, index_succ_4, index_castSucc_5, index_succ_5,
        Category.assoc, Iso.hom_inv_id_app_assoc]
  · intro Q' _ _ _ R' cg' ch' G
    obtain ⟨hex, hs⟩ := relativeKunneth_cube_factor_transport R R' cg ch cg' ch' G
    refine ⟨hex, ?_⟩
    intro A K L
    obtain ⟨beta, h0, h6, hb⟩ := hs A K L
    have hsq (i : Fin 6) : CommSq
        ((R'.coordinates.operations.pull G.b G.separated_b).map
          ((R.factors cg ch i).hom.app (K, L)))
        (beta i.castSucc).hom (beta i.succ).hom
        ((R'.factors cg' ch' i).hom.app
          ((R'.coordinates.operations.pull G.x G.separated_x).obj K,
           (R'.coordinates.operations.pull G.y G.separated_y).obj L)) := ⟨hb i⟩
    simpa only [relativeKunnethMap, relativeKunnethIso, Iso.trans_hom,
      NatTrans.comp_app, Functor.map_comp, Category.assoc,
      index_castSucc_0, index_succ_0, index_castSucc_1, index_succ_1,
      index_castSucc_2, index_succ_2, index_castSucc_3, index_succ_3,
      index_castSucc_4, index_succ_4, index_castSucc_5, index_succ_5, h0, h6] using
      ((hsq 0).horiz_comp ((hsq 1).horiz_comp ((hsq 2).horiz_comp
        ((hsq 3).horiz_comp ((hsq 4).horiz_comp (hsq 5)))))).w
  · intro Q' J
    exact relativeKunneth_closed_fibre R J

end WeilConjectures
