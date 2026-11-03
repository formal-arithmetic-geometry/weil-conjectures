/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackTensorFixedCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteDerivedPullbackTensorIdentityComposition
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackCompositionFixedCoordinates
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare

/-! Fixed-coefficient coordinate square for the finite partial tensor identity.
(blueprint: lem-sf-finite-partial-tensor-identity-fixed-coordinates)

The proof expands the prescribed pullback/tensor comparison through the full
constructible inclusion and the coefficient realization.  The two realization
units cancel, and the remaining square is the identity specialization of the
fixed-coefficient derived pullback/tensor comparison.  The latter is the
composition theorem `leftDerivedUpperStarTensorComparison_identityComposition`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem pair_map_comp {A B C : Type*}
    [Category A] [Category B] [Category C] (T : A × B ⥤ C)
    {a b c : A} {a' b' c' : B}
    (f : a ⟶ b) (g : a' ⟶ b') (h : b ⟶ c) (k : b' ⟶ c') :
    T.map (Prod.mkHom f g) ≫ T.map (Prod.mkHom h k) =
      T.map (Prod.mkHom (f ≫ h) (g ≫ k)) := by
  rw [← T.map_comp]
  rfl

private theorem pair_inverse_square {A B : Type*} [Category A] [Category B]
    (W : A × A ⥤ B) {x x' y y' : A} {z : B} (p : x ≅ x') (q : y ≅ y')
    (a : z ⟶ W.obj (x, y)) (b : z ⟶ W.obj (x', y'))
    (h : a ≫ W.map (Prod.mkHom (𝟙 x) q.hom) =
      b ≫ W.map (Prod.mkHom p.inv (𝟙 y'))) :
    a ≫ W.map (Prod.mkHom p.hom q.hom) = b := by
  have h' := congrArg (fun k ↦ k ≫ W.map (Prod.mkHom p.hom (𝟙 y'))) h
  simpa only [Category.assoc, pair_map_comp, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id, ← prod_id, W.map_id] using h'

private theorem curried_pair_inverse_square
    {B : Type*} [Category B] (F : B ⥤ B ⥤ B)
    {x x' y y' z : B} (p : x ≅ x') (q : y ≅ y')
    (a : z ⟶ (F.obj x).obj y) (b : z ⟶ (F.obj x').obj y')
    (h : a ≫ (F.obj x).map q.hom = b ≫ (F.map p.inv).app y') :
    a ≫ (Functor.uncurry.obj F).map (Prod.mkHom p.hom q.hom) = b := by
  apply pair_inverse_square (Functor.uncurry.obj F) p q a b
  simpa only [Functor.uncurry_obj_map, F.map_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h

private theorem tensor_coordinate_inverse_cancel
    {B : Type*} [Category B] (F : B ⥤ B ⥤ B)
    {x x' y y' z z' w w' : B} (p : x ≅ x') (q : y ≅ y')
    (a : z ⟶ z') (t : z' ⟶ (F.obj x).obj y)
    (b : z ⟶ w) (c : w ⟶ w') (d : w' ⟶ (F.obj x').obj y')
    (h : a ≫ t ≫ (F.obj x).map q.hom = b ≫ c ≫ d ≫ (F.map p.inv).app y') :
    a ≫ t ≫ (Functor.uncurry.obj F).map (Prod.mkHom p.hom q.hom) = b ≫ c ≫ d := by
  have h' := curried_pair_inverse_square F p q (a ≫ t) (b ≫ c ≫ d)
    (by simpa only [Category.assoc] using h)
  simpa only [Category.assoc] using h'

private theorem identity_comparison_comp
    {A B I : Type*} [Category A] [Category B]
    (R : A ⥤ B) (F : I → A ⥤ A) (G : I → B ⥤ B)
    (p : ∀ i M, R.obj ((F i).obj M) ≅ (G i).obj (R.obj M))
    {i j : I} (e : i = j) (c : F i ≅ F j ⋙ F j) (d : G i ≅ G j ⋙ G j)
    (h : ∀ M, R.map (c.hom.app M) ≫ (p j ((F j).obj M)).hom ≫
      (G j).map ((p j M).hom) = (p i M).hom ≫ d.hom.app (R.obj M))
    (M : A) :
    R.map ((eqToIso (congrArg F e.symm) ≪≫ c).hom.app M) ≫
        (p j ((F j).obj M)).hom ≫ (G j).map ((p j M).hom) =
      (p j M).hom ≫ (eqToIso (congrArg G e.symm) ≪≫ d).hom.app (R.obj M) := by
  cases e
  simpa using h M

private theorem identity_tensor_transport
    {I B : Type*} [Category B] (F : I → B ⥤ B) (W : B × B ⥤ B)
    (μ : ∀ i M L, (F i).obj (W.obj (M, L)) ⟶ W.obj ((F i).obj M, (F i).obj L))
    {i j : I} (e : i = j) (d : F i ≅ F j ⋙ F j)
    (h : ∀ M L, μ i M L ≫ W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ (F j).map (μ j M L) ≫
        μ j ((F j).obj M) ((F j).obj L)) (M L : B) :
    μ j M L ≫ W.map
        (Prod.mkHom ((eqToIso (congrArg F e.symm) ≪≫ d).hom.app M)
          ((eqToIso (congrArg F e.symm) ≪≫ d).hom.app L)) =
      (eqToIso (congrArg F e.symm) ≪≫ d).hom.app (W.obj (M, L)) ≫
        (F j).map (μ j M L) ≫ μ j ((F j).obj M) ((F j).obj L) := by
  cases e
  simpa using h M L

private theorem partial_tensor_composition_transport
    {A A' B : Type*} [Category A] [Category A'] [Category B]
    (R : A ⥤ B) (Q : A' ⥤ B) (U : A ⥤ A) (V : A' ⥤ A') (P : B ⥤ B)
    (T : A × A' ⥤ A) (W : B × B ⥤ B)
    (μ : ∀ M L, U.obj (T.obj (M, L)) ⟶ T.obj (U.obj M, V.obj L))
    (ν : W ⋙ P ⟶ P.prod P ⋙ W)
    (c : ∀ M, U.obj M ≅ U.obj (U.obj M))
    (e : ∀ L, V.obj L ≅ V.obj (V.obj L)) (d : P ≅ P ⋙ P)
    (p : ∀ M, R.obj (U.obj M) ≅ P.obj (R.obj M))
    (q : ∀ L, Q.obj (V.obj L) ≅ P.obj (Q.obj L))
    (t : ∀ M L, R.obj (T.obj (M, L)) ≅ W.obj (R.obj M, Q.obj L))
    (hp : ∀ {M N} (a : M ⟶ N),
      R.map (U.map a) ≫ (p N).hom = (p M).hom ≫ P.map (R.map a))
    (ht : ∀ {M N L K} (a : M ⟶ N) (b : L ⟶ K),
      R.map (T.map (Prod.mkHom a b)) ≫ (t N K).hom =
        (t M L).hom ≫ W.map (Prod.mkHom (R.map a) (Q.map b)))
    (hc : ∀ M, R.map (c M).hom ≫ (p (U.obj M)).hom ≫ P.map ((p M).hom) =
      (p M).hom ≫ d.hom.app (R.obj M))
    (he : ∀ L, Q.map (e L).hom ≫ (q (V.obj L)).hom ≫ P.map ((q L).hom) =
      (q L).hom ≫ d.hom.app (Q.obj L))
    (hμ : ∀ M L, R.map (μ M L) ≫ (t (U.obj M) (V.obj L)).hom ≫
      W.map (Prod.mkHom ((p M).hom) ((q L).hom)) =
      (p (T.obj (M, L))).hom ≫ P.map ((t M L).hom) ≫
        ν.app (R.obj M, Q.obj L))
    (hν : ∀ M L, ν.app (M, L) ≫
      W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ P.map (ν.app (M, L)) ≫
        ν.app (P.obj M, P.obj L)) (M : A) (L : A') :
    R.map (μ M L ≫ T.map (Prod.mkHom (c M).hom (e L).hom)) =
      R.map ((c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (V.obj L)) := by
  let : IsIso (Prod.mkHom ((p (U.obj M)).hom) ((q (V.obj L)).hom)) := by
    change IsIso ((p (U.obj M)).prod (q (V.obj L))).hom
    infer_instance
  let : IsIso (Prod.mkHom (P.map ((p M).hom)) (P.map ((q L).hom))) := by
    change IsIso ((P.mapIso (p M)).prod (P.mapIso (q L))).hom
    infer_instance
  let post := (t (U.obj (U.obj M)) (V.obj (V.obj L))).hom ≫
    W.map (Prod.mkHom ((p (U.obj M)).hom) ((q (V.obj L)).hom)) ≫
    W.map (Prod.mkHom (P.map ((p M).hom)) (P.map ((q L).hom)))
  let pre := (p (T.obj (M, L))).hom ≫ P.map ((t M L).hom)
  have hl : R.map (μ M L ≫ T.map (Prod.mkHom (c M).hom (e L).hom)) ≫ post =
      pre ≫ ν.app (R.obj M, Q.obj L) ≫
        W.map (Prod.mkHom (d.hom.app (R.obj M)) (d.hom.app (Q.obj L))) := by
    dsimp only [post, pre]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% (ht (c M).hom (e L).hom)]
    rw [pair_map_comp, pair_map_comp, hc M, he L, ← pair_map_comp]
    rw [reassoc_of% (hμ M L)]
  have hr : R.map ((c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫
      μ (U.obj M) (V.obj L)) ≫ post =
      pre ≫ d.hom.app (W.obj (R.obj M, Q.obj L)) ≫
        P.map (ν.app (R.obj M, Q.obj L)) ≫
        ν.app (P.obj (R.obj M), P.obj (Q.obj L)) := by
    dsimp only [post, pre]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hμ (U.obj M) (V.obj L))]
    rw [reassoc_of% (hp (μ M L))]
    have hn := ν.naturality (Prod.mkHom (p M).hom (q L).hom)
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
      Functor.prod_obj] at hn
    rw [← hn]
    rw [← P.map_comp_assoc, ← P.map_comp_assoc]
    simp only [Category.assoc]
    rw [hμ]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hc (T.obj (M, L)))]
    rw [← reassoc_of% (d.hom.naturality ((t M L).hom))]
  exact (cancel_mono post).1
    (hl.trans ((congrArg (fun a ↦ pre ≫ a) (hν (R.obj M) (Q.obj L))).trans hr.symm))

private def restricted_tensor_coordinates
    {A B : Type*} [Category A] [Category B] (E : A ≌ B) (F : A ⥤ A ⥤ A)
    (J K : ObjectProperty B)
    (h : ∀ (x : J.FullSubcategory) (y : K.FullSubcategory),
      J (E.functor.obj ((F.obj (E.inverse.obj x.obj)).obj (E.inverse.obj y.obj)))) :
    let G := (Functor.postcompose₂.obj E.functor).obj
      ((((Functor.whiskeringLeft₂ _).obj E.inverse).obj E.inverse).obj F)
    let T := Functor.uncurry.obj (Functor.currying.inverse.obj
      (J.lift ((J.ι.prod K.ι) ⋙ Functor.uncurry.obj G) (fun xy ↦ h xy.1 xy.2)))
    T ⋙ J.ι ⋙ E.inverse ≅ (J.ι ⋙ E.inverse).prod (K.ι ⋙ E.inverse) ⋙
      Functor.uncurry.obj F := by
  dsimp only
  refine NatIso.ofComponents
    (fun xy ↦ (E.unitIso.app
      ((((((Functor.whiskeringLeft₂ _).obj E.inverse).obj E.inverse).obj F).obj
        xy.1.obj).obj xy.2.obj)).symm) ?_
  intro xy xy' a
  change E.inverse.map
    ((E.functor.map ((F.map (E.inverse.map a.1.hom)).app (E.inverse.obj xy.2.obj)) ≫
      E.functor.map ((F.obj (E.inverse.obj xy'.1.obj)).map (E.inverse.map (𝟙 xy.2.obj)))) ≫
    (E.functor.map ((F.map (E.inverse.map (𝟙 xy'.1.obj))).app (E.inverse.obj xy.2.obj)) ≫
      E.functor.map ((F.obj (E.inverse.obj xy'.1.obj)).map (E.inverse.map a.2.hom)))) ≫
      E.unitIso.inv.app _ = E.unitIso.inv.app _ ≫
    ((F.map (E.inverse.map a.1.hom)).app (E.inverse.obj xy.2.obj) ≫
      (F.obj (E.inverse.obj xy'.1.obj)).map (E.inverse.map a.2.hom))
  rw [E.inverse.map_id, E.inverse.map_id, F.map_id]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp, ← CategoryTheory.Functor.map_comp]
  exact E.unitInv_naturality _

private def uncurry_tensor_comparison
    {B C : Type*} [Category B] [Category C]
    (F : B ⥤ B ⥤ B) {G : C ⥤ C ⥤ C} (P : B ⥤ C)
    (μ : (Functor.postcompose₂.obj P).obj F ⟶
      (((Functor.whiskeringLeft₂ _).obj P).obj P).obj G) :
    Functor.uncurry.obj F ⋙ P ⟶ P.prod P ⋙ Functor.uncurry.obj G where
  app xy := (μ.app xy.1).app xy.2
  naturality {xy xy'} a := by
    have h := (Functor.uncurry.map μ).naturality a
    dsimp only [Functor.uncurry_obj_map, Functor.uncurry_map_app,
      Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringRight, Functor.whiskeringLeft,
      Functor.comp_obj, Functor.comp_map, Functor.uncurry_obj_obj,
      Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
    simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      Functor.comp_obj, Functor.prod_obj, CategoryTheory.Functor.map_comp,
      Category.assoc] using h

private def scalar_tensor_comparison
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedTensor A Y) ⋙
        (AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor ⟶
      ((AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor).prod
          (AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor ⋙
        Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedTensor A X) :=
  uncurry_tensor_comparison (AlgebraicGeometry.ProEtale.derivedTensor A Y)
    (G := AlgebraicGeometry.ProEtale.derivedTensor A X)
    (AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison A f)

private def scalar_identity_compositor
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) :
    (AlgebraicGeometry.ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor ≅
      (AlgebraicGeometry.ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor ⋙
        (AlgebraicGeometry.ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor :=
  eqToIso (congrArg (fun f : X ⟶ X ↦
    (AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor)
    (Category.id_comp (𝟙 X)).symm) ≪≫
      AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp A (𝟙 X) (𝟙 X)

private def scalar_compositor_at
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (a : X ⟶ X) (ha : a = 𝟙 X) :
    (AlgebraicGeometry.ProEtale.upperStar A a).leftDerivedFunctor ≅
      (AlgebraicGeometry.ProEtale.upperStar A a).leftDerivedFunctor ⋙
        (AlgebraicGeometry.ProEtale.upperStar A a).leftDerivedFunctor := by
  subst a
  exact scalar_identity_compositor A X

attribute [local implicit_reducible] finiteTorConstructible
  CompactSupportFiniteProjection.coordinates
  CompactSupportFiniteProjection.torPull CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.tensor CompactSupportFiniteProjection.fixedTensor
  CompactSupportFiniteProjection.fixedDerivedPull

attribute [local irreducible] CompactSupportFiniteProjection.realization
  AlgebraicGeometry.ProEtale.derivedTensor AlgebraicGeometry.ProEtale.upperStar
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CompactSupportFiniteProjection.tensorCoordinates
  CompactSupportFiniteProjection.fixedPullRealization
  CompactSupportFiniteProjection.pullCoordinatesIso

private def pull_coordinate_component
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E n hn Y) :
    (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj
        ((S.finite.pull f).obj M) ≅
      (CompactSupportFiniteProjection.fixedDerivedPull (C := C) (E := E) (n := n) f).obj
        ((CompactSupportFiniteProjection.coordinates
          (C := C) (E := E) (n := n) (hn := hn) Y).obj M) :=
  CompactSupportFiniteProjection.fixedPullRealization S f M

private def tor_coordinate_component
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    ((finiteTorConstructible C.l E n hn X.obj.left).ι ⋙
        (CompactSupportFiniteProjection.realization
          (C := C) (E := E) (n := n) (hn := hn) X).inverse).obj
        ((CompactSupportFiniteProjection.torPull S f).obj L) ≅
      (CompactSupportFiniteProjection.fixedDerivedPull (C := C) (E := E) (n := n) f).obj
        (((finiteTorConstructible C.l E n hn Y.obj.left).ι ⋙
          (CompactSupportFiniteProjection.realization
            (C := C) (E := E) (n := n) (hn := hn) Y).inverse).obj L) :=
  CompactSupportFiniteProjection.fixedPullRealization S f ⟨L.obj, L.property.1⟩

private def tensor_coordinate_component
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D)
    (M : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj
        ((Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)).obj (M, L)) ≅
      (Functor.uncurry.obj (CompactSupportFiniteProjection.fixedTensor
        (C := C) (E := E) (n := n) X)).obj
        ((CompactSupportFiniteProjection.coordinates
          (C := C) (E := E) (n := n) (hn := hn) X).obj M,
          ((finiteTorConstructible C.l E n hn X.obj.left).ι ⋙
            (CompactSupportFiniteProjection.realization
              (C := C) (E := E) (n := n) (hn := hn) X).inverse).obj L) :=
  CompactSupportFiniteProjection.tensorCoordinates S X M L


private theorem forward_pullback_tensor_coordinates
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let R := CompactSupportFiniteProjection.coordinates
      (C := C) (E := E) (n := n) (hn := hn) X
    let RY := CompactSupportFiniteProjection.coordinates
      (C := C) (E := E) (n := n) (hn := hn) Y
    let P := CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := n) f
    let W := Functor.uncurry.obj (CompactSupportFiniteProjection.fixedTensor
      (C := C) (E := E) (n := n) X)
    let Q := (finiteTorConstructible C.l E n hn Y.obj.left).ι ⋙
      (CompactSupportFiniteProjection.realization
        (C := C) (E := E) (n := n) (hn := hn) Y).inverse
    let U := S.finite.pull f
    let V := CompactSupportFiniteProjection.torPull S f
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S Y)
    let p := pull_coordinate_component S f
    let q := tor_coordinate_component S f
    let tx := tensor_coordinate_component S X
    let ty := tensor_coordinate_component S Y
    let ν := scalar_tensor_comparison A f.hom.left
    ∀ (M : sixFunctorFiniteCategory D C E n hn Y)
      (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      R.map (CompactSupportFiniteProjection.pullbackTensorComparison S f M L).hom ≫
        (tx (U.obj M) (V.obj L)).hom ≫
        W.map (Prod.mkHom (p M).hom (q L).hom) =
      (p (T.obj (M, L))).hom ≫ P.map (ty M L).hom ≫ ν.app (RY.obj M, Q.obj L) := by
  dsimp only [pull_coordinate_component, tor_coordinate_component, tensor_coordinate_component,
    scalar_tensor_comparison, uncurry_tensor_comparison]
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  intro M L
  apply tensor_coordinate_inverse_cancel
    (CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X)
    (CompactSupportFiniteProjection.fixedPullRealization S f M)
    (CompactSupportFiniteProjection.fixedPullRealization S f ⟨L.obj, L.property.1⟩)
  exact CompactSupportFiniteProjection.pullbackTensor_fixed_coordinates S f M L

private theorem identity_pullback_coordinates
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let U := S.finite.pull (𝟙 X)
    let R := CompactSupportFiniteProjection.coordinates
      (C := C) (E := E) (n := n) (hn := hn) X
    let P := CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := n) (𝟙 X)
    let p := pull_coordinate_component S (𝟙 X)
    let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
      eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj M)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        (S.finite.pullComposition (𝟙 X) (𝟙 X)).app M
    let d := scalar_compositor_at A X.obj.left
      (𝟙 X : X ⟶ X).hom.left (by rfl)
    ∀ M, R.map (c M).hom ≫ (p (U.obj M)).hom ≫ P.map ((p M).hom) =
      (p M).hom ≫ d.hom.app (R.obj M) := by
  dsimp only
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
  let U := S.finite.pull (𝟙 X)
  let R := CompactSupportFiniteProjection.coordinates
    (C := C) (E := E) (n := n) (hn := hn) X
  let P := CompactSupportFiniteProjection.fixedDerivedPull
    (C := C) (E := E) (n := n) (𝟙 X)
  let p := pull_coordinate_component S (𝟙 X)
  let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
    eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj M)
      (Category.id_comp (𝟙 X)).symm) ≪≫
      (S.finite.pullComposition (𝟙 X) (𝟙 X)).app M
  let d := scalar_compositor_at A X.obj.left
      (𝟙 X : X ⟶ X).hom.left (by rfl)
  intro M
  have h := identity_comparison_comp R (fun f : X ⟶ X ↦ S.finite.pull f)
    (fun f ↦ CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := n) f)
    (fun f M ↦ pull_coordinate_component S f M)
    (Category.id_comp (𝟙 X)) (S.finite.pullComposition (𝟙 X) (𝟙 X))
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp A (𝟙 X.obj.left) (𝟙 X.obj.left))
    (fun N ↦ by
      simpa only [pull_coordinate_component, A, R, CompactSupportFiniteProjection.coordinates,
        Functor.comp_obj, ObjectProperty.ι_obj,
        ObjectProperty.FullSubcategory.id_hom, Over.id_left] using
        CompactSupportFiniteProjection.pullbackComposition_fixed_coordinates S (𝟙 X) (𝟙 X) N)
    M
  simpa only [scalar_compositor_at, scalar_identity_compositor, c, d, U, P, p,
    CompactSupportFiniteProjection.fixedDerivedPull,
    Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    Iso.app_hom, eqToIso.hom, eqToHom_app,
    ObjectProperty.FullSubcategory.id_hom, Over.id_left, Category.assoc] using h

private theorem identity_scalar_tensor_coordinates
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]
    {X : Scheme.{u}}
    [NatTrans.IsMonoidal (AlgebraicGeometry.ProEtale.upperStarComp A (𝟙 X) (𝟙 X)).inv] :
    let P := (AlgebraicGeometry.ProEtale.upperStar A (𝟙 X)).leftDerivedFunctor
    let W := Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedTensor A X)
    let ν := scalar_tensor_comparison A (𝟙 X)
    let d := scalar_identity_compositor A X
    ∀ M L, ν.app (M, L) ≫ W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ P.map (ν.app (M, L)) ≫
        ν.app (P.obj M, P.obj L) := by
  dsimp only [scalar_identity_compositor, scalar_tensor_comparison, uncurry_tensor_comparison]
  intro M L
  exact identity_tensor_transport
    (fun f : X ⟶ X ↦ (AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor)
    (Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedTensor A X))
    (fun f M L ↦
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison A f).app M).app L)
    (Category.id_comp (𝟙 X))
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp A (𝟙 X) (𝟙 X))
    (fun M L ↦
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_identityComposition
        A M L).symm) M L

private theorem scalar_tensor_identity_at
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]
    (X : Scheme.{u})
    [NatTrans.IsMonoidal (AlgebraicGeometry.ProEtale.upperStarComp A (𝟙 X) (𝟙 X)).inv]
    (a : X ⟶ X) (ha : a = 𝟙 X) :
    let P := (AlgebraicGeometry.ProEtale.upperStar A a).leftDerivedFunctor
    let W := Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedTensor A X)
    let ν := scalar_tensor_comparison A a
    let d := scalar_compositor_at A X a ha
    ∀ M L, ν.app (M, L) ≫ W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ P.map (ν.app (M, L)) ≫
        ν.app (P.obj M, P.obj L) := by
  subst a
  exact identity_scalar_tensor_coordinates A

private theorem identity_forward_coordinates_cached
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) X
    let R := CompactSupportFiniteProjection.coordinates
      (C := C) (E := E) (n := n) (hn := hn) X
    let Q := (finiteTorConstructible C.l E n hn X.obj.left).ι ⋙ RX.inverse
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    let P := CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := n) (𝟙 X)
    let W := Functor.uncurry.obj (CompactSupportFiniteProjection.fixedTensor
      (C := C) (E := E) (n := n) X)
    let p := pull_coordinate_component S (𝟙 X)
    let q := tor_coordinate_component S (𝟙 X)
    let t := tensor_coordinate_component S X
    let ν : W ⋙ P ⟶ P.prod P ⋙ W :=
      scalar_tensor_comparison A (𝟙 X : X ⟶ X).hom.left
    ∀ M L,
      R.map (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        (t (U.obj M) (V.obj L)).hom ≫
        W.map (Prod.mkHom (p M).hom (q L).hom) =
      (p (T.obj (M, L))).hom ≫ P.map (t M L).hom ≫ ν.app (R.obj M, Q.obj L) := by
  dsimp only
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  simpa only [CompactSupportFiniteProjection.coordinates,
    CompactSupportFiniteProjection.fixedTensor, CompactSupportFiniteProjection.fixedDerivedPull,
    Functor.uncurry_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj,
    ObjectProperty.FullSubcategory.id_hom, Over.id_left] using
    forward_pullback_tensor_coordinates S (𝟙 X)

private theorem identity_scalar_coordinates_cached (X : SixFunctorSpace D) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
    let P := CompactSupportFiniteProjection.fixedDerivedPull
      (C := C) (E := E) (n := n) (𝟙 X)
    let W := Functor.uncurry.obj (CompactSupportFiniteProjection.fixedTensor
      (C := C) (E := E) (n := n) X)
    let ν : W ⋙ P ⟶ P.prod P ⋙ W :=
      scalar_tensor_comparison A (𝟙 X : X ⟶ X).hom.left
    let d : P ≅ P ⋙ P := scalar_compositor_at A X.obj.left
      (𝟙 X : X ⟶ X).hom.left (by rfl)
    ∀ M L, ν.app (M, L) ≫
      W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ P.map (ν.app (M, L)) ≫
        ν.app (P.obj M, P.obj L) := by
  dsimp only
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact scalar_tensor_identity_at
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    X.obj.left (𝟙 X : X ⟶ X).hom.left (by rfl)

attribute [local irreducible] scalar_tensor_comparison scalar_identity_compositor
  scalar_compositor_at pull_coordinate_component tor_coordinate_component
  tensor_coordinate_component

set_option maxHeartbeats 800000 in
-- Coordinate transport involves several nested functor categories.
/-- The identity-composition equation after passage to fixed coefficient
coordinates and postcomposition with the target coordinate comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and the fixed-coefficient
calculation in `lem-sf-finite-derived-pullback-tensor-identity-composition`.
(blueprint: lem-sf-finite-partial-tensor-identity-fixed-coordinates). -/
theorem finitePartialTensor_identityComponent_coordinates
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
      eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj M)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        (S.finite.pullComposition (𝟙 X) (𝟙 X)).app M
    let d : ∀ L, V.obj L ≅ V.obj (V.obj L) := fun L ↦
      eqToIso (congrArg (fun f ↦ (CompactSupportFiniteProjection.torPull S f).obj L)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        CompactSupportFiniteProjection.torPullComposition S (𝟙 X) (𝟙 X) L
    ∀ (M : sixFunctorFiniteCategory D C E n hn X)
      (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
        (hn := hn) X).map
          ((CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
            T.map (Prod.mkHom (c M).hom (d L).hom)) ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
          (U.obj (U.obj M)) (V.obj L)).hom =
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
        (hn := hn) X).map
          ((c (T.obj (M, L))).hom ≫
            U.map ((CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom) ≫
            (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X)
              (U.obj M) (V.obj L)).hom) ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
          (U.obj (U.obj M)) (V.obj L)).hom := by
  intro U V T c e
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  let R := CompactSupportFiniteProjection.coordinates
    (C := C) (E := E) (n := n) (hn := hn) X
  let Q := (finiteTorConstructible C.l E n hn X.obj.left).ι ⋙ RX.inverse
  let P := CompactSupportFiniteProjection.fixedDerivedPull
    (C := C) (E := E) (n := n) (𝟙 X)
  let W := Functor.uncurry.obj (CompactSupportFiniteProjection.fixedTensor
    (C := C) (E := E) (n := n) X)
  let p := pull_coordinate_component S (𝟙 X)
  let q := tor_coordinate_component S (𝟙 X)
  have hp : ∀ {M N} (a : M ⟶ N),
      R.map (U.map a) ≫ (p N).hom = (p M).hom ≫ P.map (R.map a) := by
    intro M N a
    simpa only [p, pull_coordinate_component, R, U, P, Functor.comp_map,
      CompactSupportFiniteProjection.pullCoordinatesIso_hom_app] using
      (CompactSupportFiniteProjection.pullCoordinatesIso S (𝟙 X)).hom.naturality a
  let t0 : T ⋙ R ≅ R.prod Q ⋙ W := restricted_tensor_coordinates RX
    (CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X)
    (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left)
    (finiteTorConstructible C.l E n hn X.obj.left)
    ((CompactSupportFiniteProjection.domains S).1 X)
  let tNat : T ⋙ R ≅ R.prod Q ⋙ W := NatIso.ofComponents
    (fun ML ↦ tensor_coordinate_component S X ML.1 ML.2)
    (by
      intro ML ML' a
      delta tensor_coordinate_component CompactSupportFiniteProjection.tensorCoordinates
      exact t0.hom.naturality a)
  let t := tensor_coordinate_component S X
  have ht : ∀ {M N L K} (a : M ⟶ N) (b : L ⟶ K),
      R.map (T.map (Prod.mkHom a b)) ≫ (t N K).hom =
        (t M L).hom ≫ W.map (Prod.mkHom (R.map a) (Q.map b)) := by
    intro M N L K a b
    simpa only [tNat, NatIso.ofComponents_hom_app, Functor.comp_map,
      Functor.prod_map] using tNat.hom.naturality (Prod.mkHom a b)
  -- Keep the coefficient category explicit to avoid unfolding its derived functors.
  let ν : W ⋙ P ⟶ P.prod P ⋙ W := scalar_tensor_comparison
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    (𝟙 X : X ⟶ X).hom.left
  let d : P ≅ P ⋙ P := scalar_compositor_at
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    X.obj.left (𝟙 X : X ⟶ X).hom.left (by rfl)
  have hc : ∀ M, R.map (c M).hom ≫ (p (U.obj M)).hom ≫ P.map ((p M).hom) =
      (p M).hom ≫ d.hom.app (R.obj M) := by
    exact identity_pullback_coordinates S X
  have he : ∀ L, Q.map (e L).hom ≫ (q (V.obj L)).hom ≫ P.map ((q L).hom) =
      (q L).hom ≫ d.hom.app (Q.obj L) := by
    intro L
    have h := hc ⟨L.obj, L.property.1⟩
    simpa only [c, e, q, p, tor_coordinate_component, pull_coordinate_component,
      Iso.trans_hom, Iso.app_hom, eqToIso.hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.eqToHom_hom, CompactSupportFiniteProjection.torPullComposition,
      ObjectProperty.isoMk_hom, Functor.mapIso_hom, ObjectProperty.ι_map,
      R, Q, RX, V, CompactSupportFiniteProjection.coordinates,
      CompactSupportFiniteProjection.torPull, ObjectProperty.ι_obj,
      ObjectProperty.homMk_hom, ObjectProperty.homMk, ObjectProperty.lift,
      ObjectProperty.ιOfLE, U, Functor.comp_obj, Functor.comp_map] using h
  have hμ : ∀ M L,
      R.map (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        (t (U.obj M) (V.obj L)).hom ≫
        W.map (Prod.mkHom (p M).hom (q L).hom) =
      (p (T.obj (M, L))).hom ≫ P.map (t M L).hom ≫ ν.app (R.obj M, Q.obj L) := by
    exact identity_forward_coordinates_cached S X
  have hν : ∀ M L, ν.app (M, L) ≫
      W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ P.map (ν.app (M, L)) ≫
        ν.app (P.obj M, P.obj L) := by
    exact identity_scalar_coordinates_cached (C := C) (E := E) (n := n) (hn := hn) X
  intro M L
  let μ : ∀ M L, U.obj (T.obj (M, L)) ⟶ T.obj (U.obj M, V.obj L) :=
    fun M L ↦ (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom
  let out : R.obj (T.obj (U.obj (U.obj M), V.obj (V.obj L))) ≅ _ :=
    CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
      (U.obj (U.obj M)) (V.obj L)
  change R.map (μ M L ≫ T.map (Prod.mkHom (c M).hom (e L).hom)) ≫ out.hom =
    R.map ((c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (V.obj L)) ≫ out.hom
  exact congrArg (fun k ↦ k ≫ out.hom)
    (partial_tensor_composition_transport R Q U V P T W μ ν c e d p q t hp ht hc he hμ hν M L)

end WeilConjectures
