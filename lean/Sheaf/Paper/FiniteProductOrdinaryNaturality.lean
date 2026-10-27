module

public import Sheaf.Paper.FiniteTripleProductDefinitions

/-! # Naturality of the ordinary product word

Source: Steps 3 and 4 of lem-pur-finite-triple-product-normal-forms;
blueprint lem-sf-kunneth-coherence, clause (ii).
(blueprint: lem-pur-finite-product-ordinary-naturality).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem bifunctor_naturality {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (α : F ⟶ G) {X X' : C} {Y Y' : D}
    (m : X ⟶ X') (n : Y ⟶ Y') :
    (F.map m).app Y ≫ (F.obj X').map n ≫ (α.app X').app Y' =
      (α.app X).app Y ≫ (G.map m).app Y ≫ (G.obj X').map n := by
  rw [(α.app X').naturality n, ← Category.assoc, ← NatTrans.comp_app,
    α.naturality m, NatTrans.comp_app, Category.assoc]

private theorem symmetry_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) {K K' L L' : FiniteTripleProduct.D A X}
    (m : K ⟶ K') (n : L ⟶ L') :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map m).app L ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj K').map n ≫
      finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) X K' L' =
    finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) X K L ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map n).app K ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj L').map m := by
  have h := bifunctor_naturality (finiteForwardTensorSymmetryNat (ModuleCat.{u + 1} A) X)
    n m
  dsimp [Functor.flip] at h
  rw [← ((derivedTensor (ModuleCat.{u + 1} A) X).map m).naturality_assoc n]
  simpa only [finiteForwardTensorSymmetry] using h

private theorem projection_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (a : X ⟶ Y)
    {K K' : FiniteTripleProduct.D A X} {L L' : FiniteTripleProduct.D A Y}
    (m : K ⟶ K') (n : L ⟶ L') :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (R(lowerStar (ModuleCat.{u + 1} A) a).map m)).app L ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
        (R(lowerStar (ModuleCat.{u + 1} A) a).obj K')).map n ≫
      finiteProductOrdinaryProjection (ModuleCat.{u + 1} A) a K' L' =
    finiteProductOrdinaryProjection (ModuleCat.{u + 1} A) a K L ≫
      R(lowerStar (ModuleCat.{u + 1} A) a).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map m).app
            (L(upperStar (ModuleCat.{u + 1} A) a).obj L) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj K').map
            (L(upperStar (ModuleCat.{u + 1} A) a).map n)) := by
  have h := bifunctor_naturality
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) a) m n
  dsimp only [derivedTensorRightDerivedLowerStar, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map] at h
  change _ = ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) a).app K).app L ≫
    R(lowerStar (ModuleCat.{u + 1} A) a).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).map m).app
        (L(upperStar (ModuleCat.{u + 1} A) a).obj L)) ≫
    R(lowerStar (ModuleCat.{u + 1} A) a).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj K').map
        (L(upperStar (ModuleCat.{u + 1} A) a).map n)) at h
  simpa only [finiteProductOrdinaryProjection, Functor.map_comp, Category.assoc] using h

/-- The ordinary word is natural simultaneously in both inputs.
Source: the two ordinary-product naturality squares in Steps 3 and 4 of
lem-pur-finite-triple-product-normal-forms; blueprint lem-sf-kunneth-coherence (ii).
(blueprint: lem-pur-finite-product-ordinary-naturality).

Proof: apply naturality of signed symmetry to the first swap, naturality of
ordinary projection to its two inputs, and naturality of ordinary exchange to
its input. Repeat for the second swap and projection. Naturality of the inverse
direct-image compositor identifies the last square. Compose these six squares,
using functoriality of tensor, pullback and direct image. No map is inverted
except the already specified compositor. Identity input maps specialize to the
one-variable squares; zero objects and identity scheme maps require no exception. -/
theorem finiteProductOrdinary_naturality (A : Type (u + 1)) [CommRing A] [Finite A]
    {B U V T : Scheme.{u}} (a : U ⟶ B) (b : V ⟶ B)
    {r : T ⟶ U} {t : T ⟶ V} (sq : IsPullback r t a b)
    {H H' : FiniteTripleProduct.D A U} {J J' : FiniteTripleProduct.D A V}
    (m : H ⟶ H') (n : J ⟶ J') :
    finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
        (R(lowerStar (ModuleCat.{u + 1} A) a).map m)
        (R(lowerStar (ModuleCat.{u + 1} A) b).obj J) ≫
      finiteProductTensorMapRight (ModuleCat.{u + 1} A) B
        (R(lowerStar (ModuleCat.{u + 1} A) a).obj H')
        (R(lowerStar (ModuleCat.{u + 1} A) b).map n) ≫
      finiteProductOrdinary A a b sq H' J' =
    finiteProductOrdinary A a b sq H J ≫
      R(lowerStar (ModuleCat.{u + 1} A) (t ≫ b)).map
        (FiniteTripleProduct.externalMap A r t m n) := by
  let Coeff := ModuleCat.{u + 1} A
  let TB := derivedTensor Coeff B
  let TV := derivedTensor Coeff V
  let TT := derivedTensor Coeff T
  let Ra := R(lowerStar Coeff a)
  let Rb := R(lowerStar Coeff b)
  let Rt := R(lowerStar Coeff t)
  let Lb := L(upperStar Coeff b)
  let Lr := L(upperStar Coeff r)
  let Lt := L(upperStar Coeff t)
  let x := derivedBaseChangeMap Coeff sq.toCommSq
  let E := (TT.obj (Lr.obj H)).obj (Lt.obj J)
  let E' := (TT.obj (Lr.obj H')).obj (Lt.obj J')
  let em := (TT.map (Lr.map m)).app (Lt.obj J) ≫ (TT.obj (Lr.obj H')).map (Lt.map n)
  have h0 := symmetry_naturality A B (Ra.map m) (Rb.map n)
  have h1 := projection_naturality A b n (Ra.map m)
  have h2 := symmetry_naturality A V n (Lb.map (Ra.map m))
  have h4 := projection_naturality A t (Lr.map m) n
  have hx : Lb.map (Ra.map m) ≫ x.app H' = x.app H ≫ Rt.map (Lr.map m) :=
    x.naturality m
  have h3 :
      (TV.map (Lb.map (Ra.map m))).app J ≫
          (TV.obj (Lb.obj (Ra.obj H'))).map n ≫ (TV.map (x.app H')).app J' =
        (TV.map (x.app H)).app J ≫ (TV.map (Rt.map (Lr.map m))).app J ≫
          (TV.obj (Rt.obj (Lr.obj H'))).map n := by
    change (TV.map (Lb.map (Ra.map m))).app J ≫
        (TV.obj ((R(lowerStar Coeff a) ⋙ L(upperStar Coeff b)).obj H')).map n ≫
        (TV.map (x.app H')).app J' = _
    rw [(TV.map (x.app H')).naturality n,
      ← NatTrans.comp_app_assoc, ← Functor.map_comp, hx]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rfl
  have h5 := (finiteDirectImageComposition A t b).inv.naturality em
  change Rb.map (Rt.map em) ≫ (finiteDirectImageComposition A t b).inv.app E' =
    (finiteDirectImageComposition A t b).inv.app E ≫
      R(lowerStar Coeff (t ≫ b)).map em at h5
  have h2' := congrArg Rb.map h2
  have h3' := congrArg Rb.map h3
  have h4' := congrArg Rb.map h4
  simp only [CategoryTheory.Functor.map_comp] at h2' h3' h4'
  simp only [em, CategoryTheory.Functor.map_comp, Category.assoc] at h5
  unfold finiteProductOrdinary finiteProductTensorMapLeft finiteProductTensorMapRight
  dsimp only
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% h0, reassoc_of% h1]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% h2', reassoc_of% h3', reassoc_of% h4']
  rw [h5]
  simp only [FiniteTripleProduct.externalMap, CategoryTheory.Functor.map_comp]
  rfl

end AlgebraicGeometry.ProEtale
