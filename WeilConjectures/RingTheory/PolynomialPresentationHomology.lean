/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CotangentLowerShriek
public import WeilConjectures.CategoryTheory.SimplicialDerivedColimitComputation
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.TrivialKanHomotopyEquivalence

/-!
# Homology of polynomial presentations

Source: Stacks Project, Cotangent Complex, Tags 08PS and 08QI; Cohomology on Sites,
Tag 08Q9 (blueprint: lem-trf-polynomial-presentation-homology).

The polynomial category contains all small polynomial algebras, not just quotients
onto the target. `AsSmall` lifts its morphisms into the containing universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialDerivedColimit

namespace Algebra.PolynomialHomology

/-- The containing-universe category of all small polynomial presentations.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
abbrev Category {A B : CommRingCat.{u}} (f : A ⟶ B) :=
  AsSmall.{v} (CotangentSites.Presentations f)

/-- Forget the polynomial property and the universe lift, retaining the augmented algebra.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def diagram {A B : CommRingCat.{u}} (f : A ⟶ B) :
    Category.{u, v} f ⥤ Over (Under.mk f) :=
  AsSmall.down ⋙ ObjectProperty.ι _

/-- The underlying small ring of a presentation.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def rings {A B : CommRingCat.{u}} (f : A ⟶ B) : Category.{u, v} f ⥤ CommRingCat.{u} :=
  diagram f ⋙ Over.forget _ ⋙ Under.forget _

/-- The augmentation on underlying simplicial sets, with its actual component maps.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def augmentation {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) :
    Q ⋙ rings f ⋙ forget CommRingCat ⟶ (SimplicialObject.const (Type u)).obj B where
  app n := ↾((diagram f).obj (Q.obj n)).hom.right
  naturality n m θ := by
    ext x
    exact ConcreteCategory.congr_hom
      (congrArg (fun k : ((diagram f).obj (Q.obj n)).left ⟶ Under.mk f ↦ k.right)
        (Over.w ((diagram f).map (Q.map θ)))) x

/-- The constant point in the constant simplicial target.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def point {B : CommRingCat.{u}} (b : B) :
    (SimplicialObject.const (Type u)).obj PUnit ⟶
      (SimplicialObject.const (Type u)).obj B where
  app _ := ↾fun _ ↦ b

/-- The fibre over a prescribed generator value, lifted into the working universe.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def fibre {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (b : B) : SSet.{max (u + 1) v} :=
  SSet.uliftFunctor.{max (u + 1) v, u}.obj (pullback (augmentation Q) (point b))

/-- Projection from the actual augmentation fibre, lifted degreewise.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def fibreProjection {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (b : B) :
    fibre Q b ⟶ SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (Q ⋙ rings f ⋙ forget CommRingCat) :=
  SSet.uliftFunctor.{max (u + 1) v, u}.map (pullback.fst (augmentation Q) (point b))

/-- The representable simplicial set of augmentation-preserving algebra maps.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def homSet {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (T : Category.{u, v} f) :
    SSet.{max (u + 1) v} := Q ⋙ coyoneda.obj (op T)

/-- Evaluation of a representable map on a fixed element of its source algebra.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def elementEvaluation {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (T : Category.{u, v} f)
    (t : (rings f).obj T) :
    homSet Q T ⟶ SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (Q ⋙ rings f ⋙ forget CommRingCat) where
  app _ := ↾fun g ↦ ULift.up ((rings f).map g t)
  naturality n m θ := by
    ext g
    exact congrArg ULift.up (ConcreteCategory.congr_hom ((rings f).map_comp g (Q.map θ)) t)

/-- The product of the prescribed generator fibres in the containing universe.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def fibreProduct {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (T : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T) :
    SSet.{max (u + 1) v} :=
  ∏ᶜ (fun x : E ↦ fibre Q (((diagram f).obj T).hom.right (e.hom (MvPolynomial.X x))))

/-- The projection to a generator coordinate, followed by forgetting its fibre equation.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def coordinateProjection {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (T : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T) (x : E) :
    fibreProduct Q T E e ⟶ SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (Q ⋙ rings f ⋙ forget CommRingCat) :=
  Pi.π (fun y : E ↦
      fibre Q (((diagram f).obj T).hom.right (e.hom (MvPolynomial.X y)))) x ≫
    fibreProjection Q (((diagram f).obj T).hom.right (e.hom (MvPolynomial.X x)))

/-- The unique map to the constant singleton in the containing universe.
Source: Stacks 08PS (blueprint: lem-trf-polynomial-presentation-homology). -/
def toSingleton (X : SSet.{w}) :
    X ⟶ (SimplicialObject.const (Type w)).obj PUnit where
  app _ := ↾fun _ ↦ PUnit.unit

/-- The evaluation functor into the derived category, with the opposite-site encoding.
Source: Stacks 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
def evaluationDerived {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (R : Type (max (u + 1) v)) [CommRing R] :
    ((Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) v} R) :=
  evaluationComplex (Q ⋙ opOp _) ⋙ DerivedCategory.Q

/-- The degree-zero derived-colimit functor with its object formula kept explicit.
Source: Stacks 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
def colimitDiagram (bar : CategoryColimitBarSystem.{w}) (E : Type w) [SmallCategory E]
    (R : Type w) [CommRing R] :
    (Eᵒᵖ ⥤ ModuleCat.{w} R) ⥤ DerivedCategory (ModuleCat.{w} R) where
  obj F := derivedColimit bar F
  map t := (bar.models E R).derived.map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map t))
  map_id F := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl
  map_comp t s := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp]
    rfl

/-- The universal left-derived colimit on diagrams placed in degree zero.
Source: Stacks 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
def colimitDerived {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v})
    (R : Type (max (u + 1) v)) [CommRing R] :
    ((Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) v} R) :=
  colimitDiagram bar (Category.{u, v} f)ᵒᵖ R

/-- The map of derived evaluations induced by an augmented simplicial map.
Source: Stacks 08QI (blueprint: lem-trf-polynomial-presentation-homology). -/
def resolutionDerivedMap {A B : CommRingCat.{u}} {f : A ⟶ B}
    {Q Q' : SimplicialObject (Category.{u, v} f)} (h : Q ⟶ Q')
    {R : Type (max (u + 1) v)} [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R) :
    (evaluationDerived Q R).obj F ⟶ (evaluationDerived Q' R).obj F :=
  DerivedCategory.Q.map
    ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max (u + 1) v} R) ⋙
      ComplexShape.embeddingDownNat.extendFunctor _).map
        (Functor.whiskerRight (Functor.whiskerRight h (opOp _)) F))

set_option genSizeOf false in
set_option genInjectivity false in
/-- Data and their dependent normalization laws, kept abstract for efficient checking.
Source: Stacks 08PS and 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
structure ComputationPackage (Coordinates Trivial Resolution : Prop) (Comparison : Type*)
    (Normalization Naturality : Resolution → Comparison → Prop) where
  coordinates : Coordinates
  trivial : Trivial
  resolution : Resolution
  comparison : Comparison
  normalization : Normalization resolution comparison
  naturalityResolution : Naturality resolution comparison

/-- Generator coordinates and the canonically normalized derived-colimit computation.
The `Computation` parameter is the already specified general bar comparison; normalization
fixes these comparisons to its projective-resolution roof, with first-vertex bar signs.
Source: Stacks 08PS, 08QI and 08Q9
(blueprint: lem-trf-polynomial-presentation-homology). -/
abbrev ComputationData {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v}) (C : Computation bar) :=
  ComputationPackage
    (∀ (Q : SimplicialObject (Category.{u, v} f))
    (T : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T),
    (CommRingCat.ofHom MvPolynomial.C ≫ e.hom = ((diagram f).obj T).left.hom) →
    ∃ i : homSet Q T ≅ fibreProduct Q T E e,
      ∀ x : E, i.hom ≫ coordinateProjection Q T E e x =
        elementEvaluation Q T (e.hom (MvPolynomial.X x)))
    (∀ (Q : SimplicialObject (Category.{u, v} f)),
    SSet.modelCategoryQuillen.I.rlp (augmentation Q) →
    ∀ T : Category.{u, v} f,
      SSet.modelCategoryQuillen.I.rlp (toSingleton (homSet Q T)))
    (∀ (Q : SimplicialObject (Category.{u, v} f)),
    SSet.modelCategoryQuillen.I.rlp (augmentation Q) → IsResolution (Q ⋙ opOp _))
    (∀ (Q : SimplicialObject (Category.{u, v} f))
    (_hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q))
    (R : Type (max (u + 1) v)) [CommRing R],
    evaluationDerived Q R ≅ colimitDerived f bar R)
    (fun resolution comparison ↦ ∀ (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q))
    (R : Type (max (u + 1) v)) [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R),
    (comparison Q hQ R).app F = C.comparison F (Q ⋙ opOp _) (resolution Q hQ))
    (fun _resolution comparison ↦ ∀ (Q Q' : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q))
    (hQ' : SSet.modelCategoryQuillen.I.rlp (augmentation Q')) (h : Q ⟶ Q')
    (R : Type (max (u + 1) v)) [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R),
    resolutionDerivedMap h F ≫ (comparison Q' hQ' R).hom.app F =
      (comparison Q hQ R).hom.app F)

private theorem ulift_trivial.{s, t} {X Y : SSet.{s}} (p : X ⟶ Y)
    (hp : SSet.modelCategoryQuillen.I.rlp p) :
    SSet.modelCategoryQuillen.I.rlp (SSet.uliftFunctor.{t, s}.map p) := by
  have hn (n : ℕ) : HasLiftingProperty (SSet.boundary.{max s t} n).ι
      (SSet.uliftFunctor.{t, s}.map p) := by
    have := hp _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n)
    constructor
    intro a b sq
    let a' : (SSet.boundary.{s} n : SSet.{s}) ⟶ X :=
      { app := fun m ↦ ↾fun x ↦ (a.app m ⟨⟨x.val.down⟩, x.property⟩).down
        naturality := by
          intro m k θ
          ext x
          exact congrArg ULift.down (ConcreteCategory.congr_hom (a.naturality θ)
            ⟨⟨x.val.down⟩, x.property⟩) }
    let b' : (SSet.stdSimplex.{s}.obj ⦋n⦌) ⟶ Y :=
      { app := fun m ↦ ↾fun x ↦ (b.app m ⟨x.down⟩).down
        naturality := by
          intro m k θ
          ext x
          exact congrArg ULift.down (ConcreteCategory.congr_hom (b.naturality θ)
            ⟨x.down⟩) }
    let sq' : CommSq a' (SSet.boundary.{s} n).ι p b' := by
      constructor
      ext m x
      exact congrArg ULift.down (congrArg (fun t ↦ t.app m
        ⟨⟨x.val.down⟩, x.property⟩) sq.w)
    let l : SSet.stdSimplex.obj ⦋n⦌ ⟶ SSet.uliftFunctor.{t, s}.obj X :=
      { app := fun m ↦ ↾fun x ↦ ULift.up (sq'.lift.app m ⟨x.down⟩)
        naturality := by
          intro m k θ
          ext x
          exact congrArg ULift.up (ConcreteCategory.congr_hom (sq'.lift.naturality θ)
            ⟨x.down⟩) }
    exact ⟨⟨{ l := l
              fac_left := by
                ext m x
                apply ULift.ext
                exact congrArg (fun t ↦ t.app m ⟨⟨x.val.down⟩, x.property⟩) sq'.fac_left
              fac_right := by
                ext m x
                apply ULift.ext
                exact congrArg (fun t ↦ t.app m ⟨x.down⟩) sq'.fac_right }⟩⟩
  rintro _ _ _ ⟨n⟩
  exact hn n

private theorem fibre_injective {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (b : B) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((fibreProjection Q b).app n) := by
  intro x y h
  apply ULift.ext
  apply Types.ext_of_isPullback
    ((evaluation _ _).obj n |>.map_isPullback
      (IsPullback.of_hasPullback (augmentation Q) (point b)))
  · exact congrArg ULift.down h
  · apply PUnit.ext

private theorem fibre_exists {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (b : B) (n : SimplexCategoryᵒᵖ)
    (q : (rings f).obj (Q.obj n)) (hq : ((diagram f).obj (Q.obj n)).hom.right q = b) :
    ∃ x : (fibre Q b).obj n, (fibreProjection Q b).app n x = ULift.up q := by
  obtain ⟨x, hx, _⟩ := Types.exists_of_isPullback
    ((evaluation _ _).obj n |>.map_isPullback
      (IsPullback.of_hasPullback (augmentation Q) (point b))) q PUnit.unit hq
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

private theorem fibre_equation {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f)) (b : B) (n : SimplexCategoryᵒᵖ)
    (x : (fibre Q b).obj n) :
    ((diagram f).obj (Q.obj n)).hom.right (((fibreProjection Q b).app n x).down) = b :=
  congrArg (fun t ↦ t.app n x.down) (pullback.condition (f := augmentation Q) (g := point b))

set_option backward.isDefEq.respectTransparency false in
private theorem generatorImages_bijective {A B : CommRingCat.{u}} {f : A ⟶ B}
    (T U : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T)
    (he : CommRingCat.ofHom MvPolynomial.C ≫ e.hom = ((diagram f).obj T).left.hom) :
    Function.Bijective (fun g : T ⟶ U ↦ fun x : E ↦
      (⟨(rings f).map g (e.hom (MvPolynomial.X x)), by
        exact ConcreteCategory.congr_hom
          (congrArg (fun k : ((diagram f).obj T).left ⟶ Under.mk f ↦ k.right)
            (Over.w ((diagram f).map g))) (e.hom (MvPolynomial.X x))⟩ :
        {q : (rings f).obj U // ((diagram f).obj U).hom.right q =
          ((diagram f).obj T).hom.right (e.hom (MvPolynomial.X x))})) := by
  constructor
  · intro g h hgh
    apply ULift.ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Under.UnderMorphism.ext
    apply (cancel_epi e.hom).1
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      have hg := Under.w ((diagram f).map g).left
      have hh := Under.w ((diagram f).map h).left
      have he' : e.hom (MvPolynomial.C a) = ((diagram f).obj T).left.hom a :=
        ConcreteCategory.congr_hom he a
      change (rings f).map g (e.hom (MvPolynomial.C a)) =
        (rings f).map h (e.hom (MvPolynomial.C a))
      rw [he']
      exact (ConcreteCategory.congr_hom hg a).trans
        (ConcreteCategory.congr_hom hh a).symm
    · intro x
      exact congrArg Subtype.val (congrFun hgh x)
  · intro q
    let k : (rings f).obj T ⟶ (rings f).obj U :=
      e.inv ≫ CommRingCat.ofHom
        (MvPolynomial.eval₂Hom ((diagram f).obj U).left.hom.hom (fun x ↦ (q x).val))
    have hk : ((diagram f).obj T).left.hom ≫ k = ((diagram f).obj U).left.hom := by
      rw [← he]
      ext a
      simp only [k, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
      exact MvPolynomial.eval₂Hom_C _ _ a
    have hk' : k ≫ ((diagram f).obj U).hom.right = ((diagram f).obj T).hom.right := by
      apply (cancel_epi e.hom).1
      apply CommRingCat.hom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        have hU := Under.w ((diagram f).obj U).hom
        have hT := Under.w ((diagram f).obj T).hom
        have he' : e.hom (MvPolynomial.C a) = ((diagram f).obj T).left.hom a :=
          ConcreteCategory.congr_hom he a
        change ((diagram f).obj U).hom.right (k (e.hom (MvPolynomial.C a))) =
          ((diagram f).obj T).hom.right (e.hom (MvPolynomial.C a))
        simp only [k, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
        change ((diagram f).obj U).hom.right
          (MvPolynomial.eval₂Hom ((diagram f).obj U).left.hom.hom
            (fun x ↦ (q x).val) (MvPolynomial.C a)) = _
        rw [MvPolynomial.eval₂Hom_C, he']
        exact (ConcreteCategory.congr_hom hU a).trans
          (ConcreteCategory.congr_hom hT a).symm
      · intro x
        change ((diagram f).obj U).hom.right (k (e.hom (MvPolynomial.X x))) = _
        simp only [k, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
        exact (congrArg (fun z ↦ ((diagram f).obj U).hom.right z)
          (MvPolynomial.eval₂Hom_X' _ _ x)).trans (q x).property
    let g : T ⟶ U := ⟨ObjectProperty.homMk
      (Over.homMk (Under.homMk k hk) (by apply Under.UnderMorphism.ext; exact hk'))⟩
    refine ⟨g, ?_⟩
    funext x
    apply Subtype.ext
    change k (e.hom (MvPolynomial.X x)) = (q x).val
    simp only [k, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
    exact MvPolynomial.eval₂Hom_X' _ _ x

private theorem pi_obj_ext {J : Type u} (X : J → SSet.{max u v})
    (n : SimplexCategoryᵒᵖ) (z w : (∏ᶜ X).obj n)
    (h : ∀ j, (Pi.π X j).app n z = (Pi.π X j).app n w) : z = w := by
  have hh : (↾fun _ : PUnit ↦ z) = (↾fun _ : PUnit ↦ w) := by
    apply limit_obj_ext
    rintro ⟨j⟩
    ext t
    exact h j
  exact ConcreteCategory.congr_hom hh PUnit.unit

set_option backward.isDefEq.respectTransparency false in
private theorem coordinates_exists {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f))
    (T : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T)
    (he : CommRingCat.ofHom MvPolynomial.C ≫ e.hom = ((diagram f).obj T).left.hom) :
    ∃ i : homSet Q T ≅ fibreProduct Q T E e,
      ∀ x : E, i.hom ≫ coordinateProjection Q T E e x =
        elementEvaluation Q T (e.hom (MvPolynomial.X x)) := by
  classical
  let b : E → B := fun x ↦ ((diagram f).obj T).hom.right (e.hom (MvPolynomial.X x))
  have hg (n : SimplexCategoryᵒᵖ) (g : T ⟶ Q.obj n) (x : E) :
      ((diagram f).obj (Q.obj n)).hom.right ((rings f).map g (e.hom (MvPolynomial.X x))) =
        b x :=
    ConcreteCategory.congr_hom
      (congrArg (fun k : ((diagram f).obj T).left ⟶ Under.mk f ↦ k.right)
        (Over.w ((diagram f).map g))) (e.hom (MvPolynomial.X x))
  let a (x : E) : homSet Q T ⟶ fibre Q (b x) :=
    { app := fun n ↦ ↾fun g ↦ (fibre_exists Q (b x) n _ (hg n g x)).choose
      naturality := by
        intro n m θ
        ext g
        apply fibre_injective Q (b x) m
        symm
        change (fibreProjection Q (b x)).app m
            ((fibre Q (b x)).map θ _) = _
        have hn := ConcreteCategory.congr_hom ((fibreProjection Q (b x)).naturality θ)
          ((fibre_exists Q (b x) n _ (hg n g x)).choose)
        dsimp only [types_comp_apply] at hn
        exact hn.trans ((congrArg
          ((SSet.uliftFunctor.{max (u + 1) v, u}.obj
            (Q ⋙ rings f ⋙ forget CommRingCat)).map θ)
          (fibre_exists Q (b x) n _ (hg n g x)).choose_spec).trans
            ((ConcreteCategory.congr_hom
              ((elementEvaluation Q T (e.hom (MvPolynomial.X x))).naturality θ) g).symm.trans
                (fibre_exists Q (b x) m _
                  (hg m ((homSet Q T).map θ g) x)).choose_spec.symm)) }
  -- These maps retain the prescribed generator values.
  have ha (x : E) : a x ≫ fibreProjection Q (b x) =
      elementEvaluation Q T (e.hom (MvPolynomial.X x)) := by
    ext n g
    exact (fibre_exists Q (b x) n _ (hg n g x)).choose_spec
  let c : homSet Q T ⟶ fibreProduct Q T E e := Pi.lift a
  have hc (x : E) : c ≫ coordinateProjection Q T E e x =
      elementEvaluation Q T (e.hom (MvPolynomial.X x)) := by
    dsimp [c, coordinateProjection]
    rw [← Category.assoc, Pi.lift_π]
    exact ha x
  have hc_iso (n : SimplexCategoryᵒᵖ) : IsIso (c.app n) := by
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · intro g h hgh
      apply (generatorImages_bijective T (Q.obj n) E e he).injective
      funext x
      apply Subtype.ext
      have hh := congrArg (fun z ↦ (coordinateProjection Q T E e x).app n z) hgh
      have hcx := congrArg (fun t : homSet Q T ⟶ _ ↦ t.app n) (hc x)
      have hcg := ConcreteCategory.congr_hom hcx g
      have hch := ConcreteCategory.congr_hom hcx h
      exact ULift.up_injective (hcg.symm.trans (hh.trans hch))
    · intro z
      let q (x : E) : {q : (rings f).obj (Q.obj n) //
          ((diagram f).obj (Q.obj n)).hom.right q = b x} :=
        ⟨((coordinateProjection Q T E e x).app n z).down,
          fibre_equation Q (b x) n ((Pi.π (fun x ↦ fibre Q (b x)) x).app n z)⟩
      obtain ⟨g, hgq⟩ := (generatorImages_bijective T (Q.obj n) E e he).surjective q
      refine ⟨g, ?_⟩
      apply pi_obj_ext.{u, max (u + 1) v} (fun x ↦ fibre Q (b x)) n
      intro x
      apply fibre_injective Q (b x) n
      have hcg := ConcreteCategory.congr_hom (congrArg (fun t : homSet Q T ⟶ _ ↦ t.app n) (hc x)) g
      exact hcg.trans (congrArg ULift.up (congrArg Subtype.val (congrFun hgq x)))
  have : IsIso c := NatIso.isIso_of_isIso_app c
  exact ⟨asIso c, hc⟩

private theorem fibre_trivial {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q)) (b : B) :
    SSet.modelCategoryQuillen.I.rlp (toSingleton (fibre Q b)) := by
  have hs : SSet.modelCategoryQuillen.I.rlp (pullback.snd (augmentation Q) (point b)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hQ
  have hu := ulift_trivial.{u, max (u + 1) v} _ hs
  let j : SSet.uliftFunctor.{max (u + 1) v, u}.obj
      ((SimplicialObject.const (Type u)).obj PUnit) ≅
      (SimplicialObject.const (Type (max (u + 1) v))).obj PUnit :=
    { hom := toSingleton _
      inv := { app := fun _ ↦ ↾fun _ ↦ ULift.up PUnit.unit }
      hom_inv_id := by ext n x; apply ULift.ext; exact PUnit.ext _ _
      inv_hom_id := by ext n x; exact PUnit.ext _ _ }
  have : IsIso j.hom := j.isIso_hom
  have hj : SSet.modelCategoryQuillen.I.rlp j.hom :=
    MorphismProperty.rlp_of_isIso _ _
  have hj' := SSet.modelCategoryQuillen.I.rlp.comp_mem _ _ hu hj
  have hh : SSet.uliftFunctor.map (pullback.snd (augmentation Q) (point b)) ≫ j.hom =
      toSingleton (fibre Q b) := by
    ext n x
    exact PUnit.ext _ _
  rwa [hh] at hj'

private theorem product_trivial {J : Type u} (X : J → SSet.{max u v})
    (hX : ∀ j, SSet.modelCategoryQuillen.I.rlp (toSingleton (X j))) :
    SSet.modelCategoryQuillen.I.rlp (toSingleton (∏ᶜ X)) := by
  intro A B i hi
  have (j : J) := hX j i hi
  constructor
  intro a b sq
  let sqj (j : J) : CommSq (a ≫ Pi.π X j) i (toSingleton (X j)) b := by
    constructor
    ext n x
    exact PUnit.ext _ _
  exact ⟨⟨{ l := Pi.lift (fun j ↦ (sqj j).lift)
            fac_left := by
              apply Pi.hom_ext
              intro j
              simp only [Category.assoc, Pi.lift_π]
              exact (sqj j).fac_left
            fac_right := by
              ext n x
              exact PUnit.ext _ _ }⟩⟩

private theorem homSet_trivial {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q)) (T : Category.{u, v} f) :
    SSet.modelCategoryQuillen.I.rlp (toSingleton (homSet Q T)) := by
  obtain ⟨E, e, he⟩ := (AsSmall.down.obj T).property
  obtain ⟨i, _⟩ := coordinates_exists Q T E e he
  have ht := product_trivial.{u, max (u + 1) v} (fun x : E ↦
    fibre Q (((diagram f).obj T).hom.right (e.hom (MvPolynomial.X x))))
      (fun x ↦ fibre_trivial Q hQ _)
  have hi := SSet.modelCategoryQuillen.I.rlp.comp_mem i.hom _
    (MorphismProperty.rlp_of_isIso _ _) ht
  have hh : i.hom ≫ toSingleton (fibreProduct Q T E e) = toSingleton (homSet Q T) := by
    ext n x
    exact PUnit.ext _ _
  exact hh ▸ hi

private theorem resolution_of_trivial {A B : CommRingCat.{u}} {f : A ⟶ B}
    (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q)) :
    IsResolution (Q ⋙ opOp _) := by
  intro T
  let X := (Q ⋙ opOp _) ⋙ yoneda.obj T
  let i : X ≅ homSet Q T.unop :=
    { hom := { app := fun _ ↦ ↾fun g ↦ g.unop }
      inv := { app := fun _ ↦ ↾fun g ↦ g.op } }
  let p : X ⟶ (SimplicialObject.const (Type (max (u + 1) v))).obj PUnit :=
    i.hom ≫ toSingleton _
  have : IsIso i.hom := i.isIso_hom
  have hp : SSet.modelCategoryQuillen.I.rlp p :=
    SSet.modelCategoryQuillen.I.rlp.comp_mem _ _
      (MorphismProperty.rlp_of_isIso _ _) (homSet_trivial Q hQ T.unop)
  obtain ⟨g, hg, h, h₀, h₁⟩ := SSet.exists_section_homotopy_equivalence p hp
  refine ⟨p, g, ?_, ?_⟩
  · apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    refine ⟨{ h := h, h₀ := h₀, h₁ := h₁, rel := ?_ }⟩
    ext n x
    exact x.1.property.elim
  · rw [hg]
    exact Relation.EqvGen.refl _

private theorem evaluation_hom_ext {E : Type w} [SmallCategory E]
    {R : Type w} [CommRing R] (Q : SimplicialObject Eᵒᵖ)
    (F : Eᵒᵖ ⥤ ModuleCat.{w} R) {K : CochainComplex (ModuleCat.{w} R) ℤ}
    (a b : (evaluationComplex Q).obj F ⟶ K)
    (h : ∀ n : ℕ, a.f (-↑n) = b.f (-↑n)) : a = b := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : ∃ n : ℕ, -(n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    exact h n
  · exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat i
      (fun n hn ↦ hi ⟨n, hn⟩)).eq_of_src _ _

private theorem evaluation_formula_id {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) (C : Computation bar)
    {R : Type w} [CommRing R] {F G : Eᵒᵖ ⥤ ModuleCat.{w} R} (t : F ⟶ G)
    {Q Q' : SimplicialObject Eᵒᵖ} (k : Q ⟶ Q') :
    C.evaluationMap (𝟭 E) (RingHom.id R) t k =
      (evaluationComplex Q).map t ≫
        (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
          ComplexShape.embeddingDownNat.extendFunctor _).map (Functor.whiskerRight k G) := by
  apply evaluation_hom_ext Q F
  intro n
  apply (cancel_mono (evaluationTerm Q' G n).hom).1
  apply (cancel_epi (evaluationTerm Q F n).inv).1
  have h : (evaluationTerm Q F n).inv ≫
      (C.evaluationMap (𝟭 E) (RingHom.id R) t k).f (-↑n) ≫
        (evaluationTerm Q' G n).hom = t.app (Q.obj (op ⦋n⦌)) ≫ G.map (k.app (op ⦋n⦌)) := by
    ext x
    exact C.evaluationFormula (𝟭 E) (RingHom.id R) t k n x
  have ht : ((evaluationComplex Q).map t).f (-↑n) =
      (evaluationTerm Q F n).hom ≫ t.app (Q.obj (op ⦋n⦌)) ≫
        (evaluationTerm Q G n).inv := by
    exact HomologicalComplex.extendMap_f
      ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R)).map
        (Functor.whiskerLeft Q t)) ComplexShape.embeddingDownNat (i := n) rfl
  have hk : ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
      ComplexShape.embeddingDownNat.extendFunctor _).map
        (Functor.whiskerRight k G)).f (-↑n) =
      (evaluationTerm Q G n).hom ≫ G.map (k.app (op ⦋n⦌)) ≫
        (evaluationTerm Q' G n).inv := by
    exact HomologicalComplex.extendMap_f
      ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R)).map
        (Functor.whiskerRight k G)) ComplexShape.embeddingDownNat (i := n) rfl
  rw [h, HomologicalComplex.comp_f, ht, hk]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem bar_map_coefficient {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) {R : Type w} [CommRing R]
    {F G : Eᵒᵖ ⥤ ModuleCat.{w} R} (t : F ⟶ G) :
    bar.map (𝟭 E) (RingHom.id R) t = (bar.models E R).bar.map t := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : ∃ n : ℕ, -(n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    apply (cancel_epi ((bar.models E R).coordinates F n).inv).1
    apply Sigma.hom_ext
    intro c
    ext x
    have h := bar.formula (𝟭 E) (RingHom.id R) t n c x
    have h' := (bar.models E R).coefficientMap t n c x
    exact h.trans h'.symm
  · apply ((bar.models E R).positive F i (by
      by_contra h
      have hle : i ≤ 0 := by omega
      exact hi ⟨(-i).toNat, by omega⟩)).eq_of_src

set_option backward.isDefEq.respectTransparency false in
private theorem derivedMap_coefficient {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) {R : Type w} [CommRing R]
    {F G : Eᵒᵖ ⥤ ModuleCat.{w} R} (t : F ⟶ G) :
    derivedMap bar (𝟭 E) (RingHom.id R) t =
      ((colimitDiagram bar E R).map t) ≫
          derivedMap bar (𝟭 E) (RingHom.id R) (𝟙 G) := by
  dsimp only [derivedMap, derivedColimit, colimitDiagram, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map]
  rw [bar_map_coefficient, bar_map_coefficient]
  erw [(bar.models E R).bar.map_id G, DerivedCategory.Q.map_id, Category.id_comp]
  have hn := (bar.models E R).model.hom.naturality t
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  erw [← Category.assoc ((bar.models E R).model.hom.app F), ← hn,
    Category.assoc]

private theorem evaluation_identity {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) (C : Computation bar)
    {R : Type w} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{w} R)
    (Q : SimplicialObject Eᵒᵖ) :
    C.evaluationMap (𝟭 E) (RingHom.id R) (𝟙 F) (𝟙 Q) = 𝟙 _ := by
  rw [evaluation_formula_id]
  erw [(evaluationComplex Q).map_id F, Functor.whiskerRight_id',
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_naturality {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) (C : Computation bar)
    {R : Type w} [CommRing R] {F G : Eᵒᵖ ⥤ ModuleCat.{w} R} (t : F ⟶ G)
    {Q Q' : SimplicialObject Eᵒᵖ} (hQ : IsResolution Q) (hQ' : IsResolution Q')
    (k : Q ⟶ Q') :
    DerivedCategory.Q.map
        ((evaluationComplex Q).map t ≫
          (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
            ComplexShape.embeddingDownNat.extendFunctor _).map (Functor.whiskerRight k G)) ≫
        (C.comparison G Q' hQ').hom =
      (C.comparison F Q hQ).hom ≫
        ((colimitDiagram bar E R).map t) := by
  let d := derivedMap bar (𝟭 E) (RingHom.id R) (𝟙 G)
  have hd : IsIso d := by
    have h := C.identity G
    have : IsIso (d ≫ (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId R) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (derivedColimit bar G)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right d
      ((Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId R) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (derivedColimit bar G))
  apply (cancel_mono d).1
  have hi := C.naturality (𝟭 E) (RingHom.id R) (𝟙 G) hQ' hQ' (𝟙 Q')
  rw [evaluation_identity] at hi
  have hi' := (congrArg (fun z ↦ z ≫
      (ModuleCat.restrictScalars (RingHom.id R)).mapDerivedCategoryFactors.inv.app
        ((evaluationComplex Q').obj G) ≫
      (ModuleCat.restrictScalars (RingHom.id R)).mapDerivedCategory.map
        (C.comparison G Q' hQ').hom) (DerivedCategory.Q.map_id _)).symm.trans hi
  erw [Category.id_comp] at hi'
  have h := C.naturality (𝟭 E) (RingHom.id R) t hQ hQ' k
  rw [evaluation_formula_id, derivedMap_coefficient] at h
  calc
    _ = DerivedCategory.Q.map _ ≫
        ((ModuleCat.restrictScalars (RingHom.id R)).mapDerivedCategoryFactors.inv.app
          ((evaluationComplex Q').obj G) ≫
          (ModuleCat.restrictScalars (RingHom.id R)).mapDerivedCategory.map
            (C.comparison G Q' hQ').hom) := by
      rw [Category.assoc]
      exact congrArg (fun z ↦ DerivedCategory.Q.map _ ≫ z) hi'.symm
    _ = _ := h
    _ = _ := by
      dsimp only [d]
      exact (Category.assoc _ _ _).symm

private theorem comparison_coefficients {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) (C : Computation bar)
    (Q : SimplicialObject Eᵒᵖ) (hQ : IsResolution Q)
    (R : Type w) [CommRing R] {F G : Eᵒᵖ ⥤ ModuleCat.{w} R} (t : F ⟶ G) :
    (evaluationComplex Q ⋙ DerivedCategory.Q).map t ≫ (C.comparison G Q hQ).hom =
      (C.comparison F Q hQ).hom ≫
        (colimitDiagram bar E R).map t := by
  have h := comparison_naturality bar C t hQ hQ (𝟙 Q)
  have hk : (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
      ComplexShape.embeddingDownNat.extendFunctor _).map
        (Functor.whiskerRight (𝟙 Q) G) = 𝟙 _ := by
    erw [Functor.whiskerRight_id', CategoryTheory.Functor.map_id]
  dsimp only [derivedColimit] at h
  erw [hk, Category.comp_id] at h
  exact h

private theorem comparison_exists {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) (C : Computation bar)
    (Q : SimplicialObject Eᵒᵖ) (hQ : IsResolution Q) (R : Type w) [CommRing R] :
    ∃ a : evaluationComplex Q ⋙ DerivedCategory.Q ≅
      colimitDiagram bar E R,
      ∀ F : Eᵒᵖ ⥤ ModuleCat.{w} R, a.app F = C.comparison F Q hQ := by
  refine ⟨NatIso.ofComponents
    (F := evaluationComplex Q ⋙ DerivedCategory.Q)
    (G := colimitDiagram bar E R)
    (fun F ↦ C.comparison F Q hQ)
    (fun t ↦ comparison_coefficients bar C Q hQ R t), ?_⟩
  intro F
  apply Iso.ext
  rfl

private theorem comparisonFamily_exists {E : Type w} [SmallCategory E]
    (bar : CategoryColimitBarSystem.{w}) (C : Computation bar) :
    ∃ a : ∀ (Q : SimplicialObject Eᵒᵖ) (_hQ : IsResolution Q)
      (R : Type w) [CommRing R],
      evaluationComplex Q ⋙ DerivedCategory.Q ≅
        colimitDiagram bar E R,
    (∀ (Q : SimplicialObject Eᵒᵖ) (hQ : IsResolution Q) (R : Type w) [CommRing R]
      (F : Eᵒᵖ ⥤ ModuleCat.{w} R), (a Q hQ R).app F = C.comparison F Q hQ) ∧
    (∀ (Q Q' : SimplicialObject Eᵒᵖ) (hQ : IsResolution Q) (hQ' : IsResolution Q')
      (k : Q ⟶ Q') (R : Type w) [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{w} R),
      DerivedCategory.Q.map
          ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
            ComplexShape.embeddingDownNat.extendFunctor _).map (Functor.whiskerRight k F)) ≫
          ((a Q' hQ' R).app F).hom = ((a Q hQ R).app F).hom) := by
  classical
  choose a ha using comparison_exists (E := E) bar C
  refine ⟨a, ha, ?_⟩
  intro Q Q' hQ hQ' k R _ F
  rw [ha Q' hQ' R F, ha Q hQ R F]
  have h := comparison_naturality bar C (𝟙 F) hQ hQ' k
  have he := (congrArg (fun t ↦ t ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} R) ⋙
        ComplexShape.embeddingDownNat.extendFunctor _).map (Functor.whiskerRight k F))
      ((evaluationComplex Q).map_id F)).trans (Category.id_comp _)
  have ht := (colimitDiagram bar E R).map_id F
  exact (congrArg (fun t ↦ DerivedCategory.Q.map t ≫
      (C.comparison F Q' hQ').hom) he).symm.trans
    (h.trans ((congrArg (fun t ↦ (C.comparison F Q hQ).hom ≫ t)
      ht).trans (Category.comp_id _)))

/-- Polynomial resolutions compute the derived colimit, with generator-fibre coordinates.
Source: Stacks Project, Tags 08PS, 08QI and 08Q9
(blueprint: lem-trf-polynomial-presentation-homology).

Proof: (1) The full subcategory of small augmented polynomial algebras has its object
and arrow types in the containing universe; `AsSmall` only lifts its arrows.
(2) Send an augmented algebra map to its generator images. Polynomial evaluation is
its inverse, for arbitrary variable sets, because each polynomial has finite support.
The augmentation equation is equivalent to the equation on each generator, and every
simplicial operator acts componentwise. This gives `coordinates`, including empty E.
(3) Each augmentation fibre has boundary fillers and a vertex by base change of the
trivial Kan fibration. Choose fillers coordinatewise, even for infinite E; the empty
product has its unique filler. This proves `trivial`.
(4) Apply lem-weil-pbc-trivial-kan-homotopy-equivalence to obtain a section and cylinder
homotopy to each singleton. These give `resolution` (also after the harmless opposite
and universe encodings).
(5) Apply lem-trf-simplicial-derived-colimit-computation to obtain `comparison`, normalized
by its projective-resolution roof and first-vertex bar model. Its evaluation complex has
term F(Q_n) in degree -n, alternating faces, and zero positive terms.
(6) Specialize its naturality to an identity indexing functor and coefficient ring map.
For a change of F this gives naturality of the comparison natural isomorphism.
For an augmented map Q to Q', use the
identity coefficient transformation; the bar map is the identity on every generator.
This gives `naturalityResolution`, without choosing homotopy inverses for the comparison. -/
theorem computationData_exists {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v}) (C : Computation bar) :
    Nonempty (ComputationData f bar C) := by
  classical
  obtain ⟨comp, hcomp, hnat⟩ :=
    comparisonFamily_exists (E := (Category.{u, v} f)ᵒᵖ) bar C
  let res := fun (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q)) ↦ resolution_of_trivial Q hQ
  refine ⟨{ coordinates := coordinates_exists
            trivial := homSet_trivial
            resolution := res
            comparison := fun Q hQ R _ ↦ comp (Q ⋙ opOp _) (res Q hQ) R
            normalization := fun Q hQ R _ F ↦
              hcomp (Q ⋙ opOp _) (res Q hQ) R F
            naturalityResolution := fun Q Q' hQ hQ' h R _ F ↦
              hnat (Q ⋙ opOp _) (Q' ⋙ opOp _) (res Q hQ) (res Q' hQ')
                (Functor.whiskerRight h (opOp _)) R F }⟩

end Algebra.PolynomialHomology
