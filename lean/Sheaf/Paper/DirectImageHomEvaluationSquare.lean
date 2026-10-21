/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.SixFunctors.EtaleHomComparisonModels
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive

/-! # Ordinary direct-image and internal-Hom evaluation scalar square

Source: blueprint, sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom,
proof paragraphs 1 and 4; Stacks Project, Tags 07A4 and 0D6D
(blueprint: lem-coef-direct-image-hom-evaluation-square).

The helpers spell out the specified arrows using the published ordinary unbounded
small-etale operations. Evaluation is written in the node's Hom-tensor-input order;
the canonical signed symmetry converts the library's input-tensor-Hom convention.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.DirectImageHomEvaluation

/-- Evaluation in Hom-tensor-input order, using the canonical signed symmetry.
Source: blueprint thm-coef-finite-hom, proof paragraph 1
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def evaluation (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (L N : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)).obj L ⟶ N :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app
      (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)).app L ≫
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) L).counit.app N

/-- The specified map u: transpose of scalar extension of evaluation, with the
canonical tensor comparison. No inverse of u is used.
Source: blueprint thm-coef-finite-hom, proof paragraph 1
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def homComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (Y : Scheme.{u}) (L N : DerivedCategoryModule A Y) :
    (scalarExtension φ Y).obj
        (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) Y).obj
        (op ((scalarExtension φ Y).obj L))).obj ((scalarExtension φ Y).obj N) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} B)
    ((scalarExtension φ Y).obj L)).homEquiv _ _
      (((derivedTensorSymmetry (ModuleCat.{u + 1} B) Y).hom.app
          ((scalarExtension φ Y).obj L)).app
          ((scalarExtension φ Y).obj
            (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) ≫
        (etaleHomTensorComparison Y φ
          (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N) L).hom ≫
        (scalarExtension φ Y).map (evaluation A Y L N))

/-- The map w is u followed by internal Hom applied to the arbitrary map b.
Source: blueprint thm-coef-finite-hom, proof paragraph 4, transposing comparisons
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def homMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (Y : Scheme.{u}) (L N : DerivedCategoryModule A Y)
    (N' : DerivedCategoryModule B Y) (b : (scalarExtension φ Y).obj N ⟶ N') :=
  homComparison φ Y L N ≫
    ((derivedHom (ModuleCat.{u + 1} B) Y).obj
      (op ((scalarExtension φ Y).obj L))).map b

/-- The map h is the ordinary scalar direct-image mate c, followed by Rf_*(w).
The existing scalarMate is exactly the adjunct of extended ordinary counit.
Source: blueprint thm-coef-finite-hom, proof paragraph 4
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def directImageMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L N : DerivedCategoryModule A Y) (N' : DerivedCategoryModule B Y)
    (b : (scalarExtension φ Y).obj N ⟶ N') :=
  (scalarMate φ f).app
      (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N) ≫
    (Functor.rightDerivedFunctor (lowerStar (ModuleCat.{u + 1} B) f)).map
      (homMap φ Y L N N' b)

/-- The ordinary evaluation pairing e_A: tensor the geometric counit with L,
then evaluate. Source: blueprint thm-coef-finite-hom, proof paragraph 4
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def ordinaryPairing (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L N : DerivedCategoryModule A Y) :=
  derivedTensorHom (ModuleCat.{u + 1} A)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
        (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) (𝟙 L) ≫
    evaluation A Y L N

/-- The specified iota, factored as scalar tensor comparison followed by the inverse
scalar/pullback identification on the first tensor factor.
Source: blueprint thm-coef-finite-hom, proof paragraph 4; Stacks 07A4, 0D6D
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def sourceComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :=
  (etaleHomTensorComparison Y φ
      ((Functor.leftDerivedFunctor (upperStar (ModuleCat.{u + 1} A) f)).obj T) L).symm ≪≫
    (((derivedTensor (ModuleCat.{u + 1} B) Y).mapIso
      ((scalarPullbackIso φ f).app T).symm).app ((scalarExtension φ Y).obj L))

/-- The specified p_h: ordinary geometric inverse transpose of h, then evaluation.
Source: blueprint thm-coef-finite-hom, proof paragraph 4
(blueprint: lem-coef-direct-image-hom-evaluation-square). -/
def transposedPairing {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L N : DerivedCategoryModule A Y) (N' : DerivedCategoryModule B Y)
    (b : (scalarExtension φ Y).obj N ⟶ N') :=
  derivedTensorHom (ModuleCat.{u + 1} B)
      ((Functor.leftDerivedFunctor (upperStar (ModuleCat.{u + 1} B) f)).map
          (directImageMap φ f L N N' b) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          (((derivedHom (ModuleCat.{u + 1} B) Y).obj
            (op ((scalarExtension φ Y).obj L))).obj N'))
      (𝟙 ((scalarExtension φ Y).obj L)) ≫
    evaluation B Y ((scalarExtension φ Y).obj L) N'

private theorem swapped_evaluation_transpose
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C) (s : T ≅ T.flip)
    (K : C) (H : C ⥤ C) (adj : T.obj K ⊣ H)
    (Q N N' : C) (e : (T.obj Q).obj K ⟶ N) (b : N ⟶ N')
    (hs : (s.hom.app Q).app K ≫ (s.hom.app K).app Q = 𝟙 _) :
    (T.map (adj.homEquiv _ _ ((s.hom.app K).app Q ≫ e) ≫ H.map b)).app K ≫
        (s.hom.app (H.obj N')).app K ≫ adj.counit.app N' = e ≫ b := by
  have hn := congr_app
    (s.hom.naturality (adj.homEquiv _ _ ((s.hom.app K).app Q ≫ e) ≫ H.map b)) K
  dsimp only [NatTrans.comp_app, Functor.flip_obj_obj, Functor.flip_map_app] at hn
  have he := (adj.homEquiv Q N').symm_apply_apply (((s.hom.app K).app Q ≫ e) ≫ b)
  rw [adj.homEquiv_counit] at he
  rw [← Category.assoc, hn, Category.assoc, ← adj.homEquiv_naturality_right, he,
    ← Category.assoc, ← Category.assoc, hs, Category.id_comp]

private theorem homMap_evaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (Y : Scheme.{u}) (L N : DerivedCategoryModule A Y)
    (N' : DerivedCategoryModule B Y) (b : (scalarExtension φ Y).obj N ⟶ N') :
    ((derivedTensor (ModuleCat.{u + 1} B) Y).map (homMap φ Y L N N' b)).app
        ((scalarExtension φ Y).obj L) ≫
        evaluation B Y ((scalarExtension φ Y).obj L) N' =
      (etaleHomTensorComparison Y φ
        (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N) L).hom ≫
        (scalarExtension φ Y).map (evaluation A Y L N) ≫ b := by
  simpa only [homMap, homComparison, evaluation, Category.assoc] using
    swapped_evaluation_transpose
    (derivedTensor (ModuleCat.{u + 1} B) Y)
    (derivedTensorSymmetry (ModuleCat.{u + 1} B) Y)
    ((scalarExtension φ Y).obj L)
    ((derivedHom (ModuleCat.{u + 1} B) Y).obj (op ((scalarExtension φ Y).obj L)))
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} B) ((scalarExtension φ Y).obj L))
    ((scalarExtension φ Y).obj
      (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N))
    ((scalarExtension φ Y).obj N) N'
    ((etaleHomTensorComparison Y φ
      (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N) L).hom ≫
      (scalarExtension φ Y).map (evaluation A Y L N))
    b (derivedTensorSymmetry_involutive B Y _ _)

private theorem directImageMap_transpose
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L N : DerivedCategoryModule A Y) (N' : DerivedCategoryModule B Y)
    (b : (scalarExtension φ Y).obj N ⟶ N') :
    (Functor.leftDerivedFunctor (upperStar (ModuleCat.{u + 1} B) f)).map
        (directImageMap φ f L N N' b) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          (((derivedHom (ModuleCat.{u + 1} B) Y).obj
            (op ((scalarExtension φ Y).obj L))).obj N') =
      (scalarPullbackIso φ f).hom.app
          ((Functor.rightDerivedFunctor (lowerStar (ModuleCat.{u + 1} A) f)).obj
            (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) ≫
        (scalarExtension φ Y).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
            (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) ≫
        homMap φ Y L N N' b := by
  let adjA := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let adjB := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  have hc := mateEquiv_counit adjA adjB
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom)
    (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)
  have hn := adjB.counit.naturality (homMap φ Y L N N' b)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  dsimp only [adjA, adjB, TwoSquare.mk] at hc hn
  dsimp only [directImageMap]
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  rw [show
    (Functor.leftDerivedFunctor (upperStar (ModuleCat.{u + 1} B) f)).map
        ((scalarMate φ f).app (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
        ((scalarExtension φ Y).obj
          (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) = _ from hc]
  rw [Category.assoc]

/-- The specified ordinary direct-image/internal-Hom evaluation scalar square.
Source: blueprint thm-coef-finite-hom, proof paragraphs 1 and 4
(blueprint: lem-coef-direct-image-hom-evaluation-square).

Proof plan (the six steps of the DAG node):
1. Put Q = H_A(L,N), T = Rf_*Q, D = f_A^*T, and d = alpha_A,Q.
   The tensor comparison mu and pullback comparison a give
   iota = (a_T inverse tensor 1) after mu_D,L (07A4 and 0D6D;
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-sfb-ringed-derived-monoidal-comparisons).
2. By the defining geometric adjunction of def-kun-projection-formula-map,
   the inverse adjunct of c is t = F(d) after a_T. No inverse of c is taken.
3. Naturality of that geometric counit at w makes the inverse adjunct of
   h = Rf_*(w) after c equal to w after t.
4. The tensor-Hom adjunction (lem-sf-ringed-derived-tensor-hom-adjunction and
   def-coef-ringed-tensor-hom-model) defining u and naturality of its evaluation
   at b give ev_B after (w tensor 1) = b after F(ev_A) after mu_Q,L inverse.
5. Simultaneous naturality of mu at (d,1_L) identifies mu_Q,L inverse after
   (F(d) tensor 1) with F(d tensor 1) after mu_D,L inverse.
6. Substitute steps 2--5 in p_h. Functoriality combines F(ev_A) and
   F(d tensor 1) into F(e_A); the remaining comparisons are iota inverse.
   This gives exactly b after F(e_A) after iota inverse, for arbitrary b.
-/
theorem square {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L N : DerivedCategoryModule A Y) (N' : DerivedCategoryModule B Y)
    (b : (scalarExtension φ Y).obj N ⟶ N') :
    transposedPairing φ f L N N' b =
      (sourceComparison φ f
        ((Functor.rightDerivedFunctor (lowerStar (ModuleCat.{u + 1} A) f)).obj
          (((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N)) L).inv ≫
        (scalarExtension φ Y).map (ordinaryPairing A f L N) ≫ b := by
  let Q := ((derivedHom (ModuleCat.{u + 1} A) Y).obj (op L)).obj N
  let d := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app Q
  have hμ :
      ((derivedTensor (ModuleCat.{u + 1} B) Y).map ((scalarExtension φ Y).map d)).app
          ((scalarExtension φ Y).obj L) ≫ (etaleHomTensorComparison Y φ Q L).hom =
        (etaleHomTensorComparison Y φ _ L).hom ≫
          (scalarExtension φ Y).map (((derivedTensor (ModuleCat.{u + 1} A) Y).map d).app L) :=
    (etaleHomTensorComparison_existsUnique Y φ).choose_spec.1.1 d L
  simp only [transposedPairing, derivedTensorHom]
  rw [directImageMap_transpose]
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.id_obj, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [homMap_evaluation φ Y L N N' b]
  rw [reassoc_of% hμ]
  simp only [sourceComparison, ordinaryPairing, derivedTensorHom,
    Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
    CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Etale.DirectImageHomEvaluation
