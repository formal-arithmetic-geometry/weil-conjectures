/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Colimit.Module

/-! # Coherent common-stage pair functor descent

Source: blueprint sketches 32, finite common-stage principle, and 42,
Proposition `prop:pseudocone-functor`, Theorems `thm:pair-universal` and
`thm:karoubi-universal` (blueprint: lem-sbc-coherent-pair-functor-descent).
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CommonStage

-- Bundling the category carriers puts both independent category universes in a maximum.
set_option linter.checkUnivs false in
/-- Normalized additive transition diagrams. Source: sketch 42, finite-stage transitions
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Diagram (I : Type w) [PartialOrder I] where
  C : I → Type u
  [category : ∀ i, Category.{v} (C i)]
  [preadditive : ∀ i, Preadditive (C i)]
  [biproducts : ∀ i, HasFiniteBiproducts (C i)]
  U : ∀ {i j}, i ≤ j → C i ⥤ C j
  [additive : ∀ {i j} (h : i ≤ j), (U h).Additive]
  unit : ∀ i, U (le_refl i) = 𝟭 (C i)
  a : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k), U h ⋙ U h' ≅ U (h.trans h')
  a_left : ∀ {i j} (h : i ≤ j),
    a (le_refl i) h =
      Functor.isoWhiskerRight (eqToIso (unit i)) (U h) ≪≫ (U h).leftUnitor
  a_right : ∀ {i j} (h : i ≤ j),
    a h (le_refl j) =
      Functor.isoWhiskerLeft (U h) (eqToIso (unit j)) ≪≫ (U h).rightUnitor
  pentagon : ∀ {i j k l} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
    (U h'').map ((a h h').hom.app X) ≫ (a (h.trans h') h'').hom.app X =
      (a h' h'').hom.app ((U h).obj X) ≫ (a h (h'.trans h'')).hom.app X

attribute [instance] Diagram.category Diagram.preadditive Diagram.biproducts Diagram.additive

variable {I : Type w} [PartialOrder I]

/-- Pair objects. Source: sketch 42, Definition `def:pair-objects`
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Pair (A : Diagram.{w, u, v} I) := Σ i, A.C i

/-- A common-stage representative. Source: sketch 42, common-stage morphism representatives
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Rep (A : Diagram.{w, u, v} I) (X Y : Pair A) where
  stage : I
  source_le : X.1 ≤ stage
  target_le : Y.1 ≤ stage
  arrow : (A.U source_le).obj X.2 ⟶ (A.U target_le).obj Y.2

/-- Transport by the specified associators, with the inverse on the source.
Source: sketch 42, transport (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def transport {A : Diagram.{w, u, v} I} {X Y : Pair A} (r : Rep A X Y)
    {n : I} (h : r.stage ≤ n) :
    (A.U (r.source_le.trans h)).obj X.2 ⟶ (A.U (r.target_le.trans h)).obj Y.2 :=
  (A.a r.source_le h).inv.app X.2 ≫ (A.U h).map r.arrow ≫
    (A.a r.target_le h).hom.app Y.2

/-- Equality after transport to a common overfield. Source: sketch 42, common-stage equality
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def EventuallyEqual {A : Diagram.{w, u, v} I} {X Y : Pair A}
    (r s : Rep A X Y) : Prop :=
  ∃ (n : I) (h : r.stage ≤ n) (h' : s.stage ≤ n), transport r h = transport s h'

/-- The actual quotient of representatives; no choice of a category is hidden in its Hom sets.
Source: sketch 42, pair morphisms (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Hom (A : Diagram.{w, u, v} I) (X Y : Pair A) := Quot (@EventuallyEqual I _ A X Y)

/-- The class of a representative. Source: sketch 42, pair morphisms
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def repr {A : Diagram.{w, u, v} I} {X Y : Pair A} (r : Rep A X Y) : Hom A X Y :=
  Quot.mk _ r

/-- Operations and laws on the explicit quotient Hom types.
Source: sketch 42 (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure PairStructure (A : Diagram.{w, u, v} I) where
  [group : ∀ X Y : Pair A, AddCommGroup (Hom A X Y)]
  id : ∀ X : Pair A, Hom A X X
  comp : ∀ {X Y Z : Pair A}, Hom A X Y → Hom A Y Z → Hom A X Z
  id_comp : ∀ {X Y : Pair A} (f : Hom A X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Pair A} (f : Hom A X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : Pair A} (f : Hom A W X) (g : Hom A X Y) (h : Hom A Y Z),
    comp (comp f g) h = comp f (comp g h)
  add_comp : ∀ {X Y Z : Pair A} (f g : Hom A X Y) (h : Hom A Y Z),
    comp (f + g) h = comp f h + comp g h
  comp_add : ∀ {X Y Z : Pair A} (f : Hom A X Y) (g h : Hom A Y Z),
    comp f (g + h) = comp f g + comp f h


/-- The category carrier records which canonical operations are in use.
Source: sketch 42, pair category (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def PairStructure.Obj {A : Diagram.{w, u, v} I} (_R : PairStructure A) := Pair A

/-- Category structure assembled from the stated pair laws, with the actual quotient Hom.
Source: sketch 42, composition laws (blueprint: lem-sbc-coherent-pair-functor-descent). -/
instance pairCategory {A : Diagram.{w, u, v} I} (R : PairStructure A) : Category R.Obj where
  Hom := Hom A
  id := R.id
  comp := R.comp
  id_comp := R.id_comp
  comp_id := R.comp_id
  assoc := R.assoc

/-- Preadditivity assembled from the pair laws. Source: sketch 42, composition laws
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
instance pairPreadditive {A : Diagram.{w, u, v} I} (R : PairStructure A) :
    Preadditive R.Obj where
  homGroup := R.group
  add_comp := fun _ _ _ ↦ R.add_comp
  comp_add := fun _ _ _ ↦ R.comp_add

/-- The class map with its categorical type made explicit. Source: sketch 42, pair morphisms
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def PairStructure.repr {A : Diagram.{w, u, v} I} (R : PairStructure A)
    {X Y : R.Obj} (r : Rep A X Y) : X ⟶ Y := CategoryTheory.CommonStage.repr r

/-- The canonical laws prescribe every operation on representatives; the equality clause
also asserts that the quotient relation is exactly eventual equality, without enlarging it.
Source: sketch 42, pair calculus (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure PairStructure.IsCanonical {A : Diagram.{w, u, v} I} (R : PairStructure A) : Prop where
  equality : ∀ {X Y : R.Obj} (r s : Rep A X Y),
    R.repr r = R.repr s ↔ EventuallyEqual r s
  identity : ∀ X : R.Obj,
    𝟙 X = R.repr ⟨X.1, le_refl _, le_refl _, 𝟙 ((A.U (le_refl X.1)).obj X.2)⟩
  composition : ∀ {X Y Z : R.Obj} (r : Rep A X Y) (s : Rep A Y Z)
      (n : I) (hr : r.stage ≤ n) (hs : s.stage ≤ n),
    R.repr r ≫ R.repr s =
      R.repr ⟨n, r.source_le.trans hr, s.target_le.trans hs,
        transport r hr ≫ transport s hs⟩
  addition : ∀ {X Y : R.Obj} (r s : Rep A X Y)
      (n : I) (hr : r.stage ≤ n) (hs : s.stage ≤ n),
    R.repr r + R.repr s =
      R.repr ⟨n, r.source_le.trans hr, r.target_le.trans hr,
        transport r hr + transport s hs⟩
  zero : ∀ {X Y : R.Obj} (n : I) (hx : X.1 ≤ n) (hy : Y.1 ≤ n),
    (0 : X ⟶ Y) = R.repr ⟨n, hx, hy, 0⟩
  negation : ∀ {X Y : R.Obj} (r : Rep A X Y),
    -(R.repr r) = R.repr { r with arrow := -r.arrow }

/-- Stage functors with specified comparison isomorphisms, before imposing coherence.
Source: sketch 42, pseudocone comparisons (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Family (A B : Diagram.{w, u, v} I) where
  φ : ∀ i, A.C i ⥤ B.C i
  [additive : ∀ i, (φ i).Additive]
  b : ∀ {i j} (h : i ≤ j), φ i ⋙ B.U h ≅ A.U h ⋙ φ j

attribute [instance] Family.additive

/-- The normalized unit and tower equations, retaining both diagrams' associators.
Source: sketch 42, pseudocone tower (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure Family.Coherent {A B : Diagram.{w, u, v} I} (Φ : Family A B) : Prop where
  unit : ∀ i,
    Φ.b (le_refl i) =
      Functor.isoWhiskerLeft (Φ.φ i) (eqToIso (B.unit i)) ≪≫ (Φ.φ i).rightUnitor ≪≫
        (Φ.φ i).leftUnitor.symm ≪≫
          Functor.isoWhiskerRight (eqToIso (A.unit i)).symm (Φ.φ i)
  tower : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) (X : A.C i),
    (B.a h h').hom.app ((Φ.φ i).obj X) ≫ (Φ.b (h.trans h')).hom.app X =
      (B.U h').map ((Φ.b h).hom.app X) ≫
        (Φ.b h').hom.app ((A.U h).obj X) ≫ (Φ.φ k).map ((A.a h h').hom.app X)

/-- The descended object formula. Source: sketch 42, pseudocone functor
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.obj {A B : Diagram.{w, u, v} I} (Φ : Family A B) (X : Pair A) : Pair B :=
  ⟨X.1, (Φ.φ X.1).obj X.2⟩

/-- The descended representative formula, with `b` at the source and its inverse at the target.
Source: sketch 42, pseudocone functor (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.rep {A B : Diagram.{w, u, v} I} (Φ : Family A B) {X Y : Pair A}
    (r : Rep A X Y) : Rep B (Φ.obj X) (Φ.obj Y) where
  stage := r.stage
  source_le := r.source_le
  target_le := r.target_le
  arrow := (Φ.b r.source_le).hom.app X.2 ≫ (Φ.φ r.stage).map r.arrow ≫
    (Φ.b r.target_le).inv.app Y.2

/-- The identity family, using only canonical unitors.
Source: sketch 42, pair universal property (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.identity (A : Diagram.{w, u, v} I) : Family A A where
  φ i := 𝟭 (A.C i)
  b h := (A.U h).leftUnitor ≪≫ (A.U h).rightUnitor.symm

/-- Composite comparisons are obtained by whiskering the two given comparisons.
Source: sketch 42, pair universal property (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Family.comp {A B C : Diagram.{w, u, v} I} (Φ : Family A B) (Θ : Family B C) :
    Family A C where
  φ i := Φ.φ i ⋙ Θ.φ i
  b h := (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft (Φ.φ _) (Θ.b h) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Φ.b h) (Θ.φ _) ≪≫
      Functor.associator _ _ _

/-- Compatible transformations are the stage naturality squares with the comparisons.
Source: sketch 42, pseudocone morphisms (blueprint: lem-sbc-coherent-pair-functor-descent). -/
def Compatible {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) : Prop :=
  ∀ {i j} (h : i ≤ j) (X : A.C i),
    (Φ.b h).hom.app X ≫ (η j).app ((A.U h).obj X) =
      (B.U h).map ((η i).app X) ≫ (Ψ.b h).hom.app X

/-- Characterization of the functor by its formulas on all objects and representatives.
`HEq` only accommodates the displayed object equality; it imposes equality of the arrows.
Source: sketch 42, pseudocone functor (blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure IsDescent {A B : Diagram.{w, u, v} I} (RA : PairStructure A) (RB : PairStructure B)
    (Φ : Family A B) (F : RA.Obj ⥤ RB.Obj) : Prop where
  obj : ∀ X, F.obj X = Φ.obj X
  map : ∀ {X Y : RA.Obj} (r : Rep A X Y),
    HEq (F.map (RA.repr r)) (RB.repr (Φ.rep r))
  additive : F.Additive

/-- The component `[E, η_E,K]`, written using the literal identity transition to make its
source and target types explicit. Source: sketch 42, pseudocone morphisms
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def transformationRep {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
    (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (X : Pair A) : Rep B (Φ.obj X) (Ψ.obj X) :=
  ⟨X.1, le_refl _, le_refl _, (B.U (le_refl X.1)).map ((η X.1).app X.2)⟩

-- The independently variable object and Hom universes are bundled in the same maximum.
set_option linter.checkUnivs false in
/-- All the asserted descent data, with every construction characterized on representatives.
This is a specification, not a choice from an unspecified existence theorem: the pair Hom
sets are the explicit quotient, and the canonical formulas determine all operations and maps.
Source: sketch 42, pair and Karoubi universal properties
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
structure DescentSystem (I : Type w) [PartialOrder I] where
  pair : ∀ A : Diagram.{w, u, v} I, PairStructure A
  canonical : ∀ A, (pair A).IsCanonical
  [biproducts : ∀ A, HasFiniteBiproducts (pair A).Obj]
  descend : ∀ {A B : Diagram.{w, u, v} I} (Φ : Family A B),
    Φ.Coherent → (pair A).Obj ⥤ (pair B).Obj
  formula : ∀ {A B : Diagram.{w, u, v} I} (Φ : Family A B) (h : Φ.Coherent),
    IsDescent (pair A) (pair B) Φ (descend Φ h)
  identity_coherent : ∀ A : Diagram.{w, u, v} I, (Family.identity A).Coherent
  composition_coherent : ∀ {A B C : Diagram.{w, u, v} I}
      (Φ : Family A B) (Θ : Family B C),
    Φ.Coherent → Θ.Coherent → (Φ.comp Θ).Coherent
  identity_preserved : ∀ A : Diagram.{w, u, v} I,
    descend (Family.identity A) (identity_coherent A) = 𝟭 (pair A).Obj
  composition_preserved : ∀ {A B C : Diagram.{w, u, v} I}
      (Φ : Family A B) (Θ : Family B C) (hΦ : Φ.Coherent) (hΘ : Θ.Coherent),
    descend (Φ.comp Θ) (composition_coherent Φ Θ hΦ hΘ) = descend Φ hΦ ⋙ descend Θ hΘ
  transformation : ∀ {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
      (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i),
    Compatible η → (descend Φ hΦ ⟶ descend Ψ hΨ)
  transformation_formula : ∀ {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
      (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i)
      (hη : Compatible η) (X : (pair A).Obj),
    HEq ((transformation hΦ hΨ η hη).app X) ((pair B).repr (transformationRep η X))
  identity_compatible : ∀ {A B : Diagram.{w, u, v} I} (Φ : Family A B),
    Compatible (fun i ↦ 𝟙 (Φ.φ i))
  transformation_identity : ∀ {A B : Diagram.{w, u, v} I}
      (Φ : Family A B) (hΦ : Φ.Coherent),
    transformation hΦ hΦ (fun i ↦ 𝟙 (Φ.φ i)) (identity_compatible Φ) = 𝟙 (descend Φ hΦ)
  vertical_compatible : ∀ {A B : Diagram.{w, u, v} I} {Φ Ψ Ω : Family A B}
      (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (δ : ∀ i, Ψ.φ i ⟶ Ω.φ i),
    Compatible η → Compatible δ → Compatible (fun i ↦ η i ≫ δ i)
  transformation_composition : ∀ {A B : Diagram.{w, u, v} I} {Φ Ψ Ω : Family A B}
      (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (hΩ : Ω.Coherent)
      (η : ∀ i, Φ.φ i ⟶ Ψ.φ i) (δ : ∀ i, Ψ.φ i ⟶ Ω.φ i)
      (hη : Compatible η) (hδ : Compatible δ),
    transformation hΦ hΩ (fun i ↦ η i ≫ δ i) (vertical_compatible η δ hη hδ) =
      transformation hΦ hΨ η hη ≫ transformation hΨ hΩ δ hδ
  transformation_equations : ∀ {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
      (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η θ : ∀ i, Φ.φ i ⟶ Ψ.φ i)
      (hη : Compatible η) (hθ : Compatible θ),
    (∀ i, η i = θ i) → transformation hΦ hΨ η hη = transformation hΦ hΨ θ hθ
  karoubi_additive : ∀ {A B : Diagram.{w, u, v} I}
      (Φ : Family A B) (hΦ : Φ.Coherent),
    ((Idempotents.functorExtension₂ _ _).obj (descend Φ hΦ)).Additive
  karoubi_object : ∀ {A B : Diagram.{w, u, v} I}
      (Φ : Family A B) (hΦ : Φ.Coherent) (P : Idempotents.Karoubi (pair A).Obj),
    (((Idempotents.functorExtension₂ _ _).obj (descend Φ hΦ)).obj P).X =
      (descend Φ hΦ).obj P.X ∧
    HEq (((Idempotents.functorExtension₂ _ _).obj (descend Φ hΦ)).obj P).p
      ((descend Φ hΦ).map P.p)
  karoubi_arrow : ∀ {A B : Diagram.{w, u, v} I}
      (Φ : Family A B) (hΦ : Φ.Coherent)
      {P Q : Idempotents.Karoubi (pair A).Obj} (f : P ⟶ Q),
    HEq (((Idempotents.functorExtension₂ _ _).obj (descend Φ hΦ)).map f).f
      ((descend Φ hΦ).map f.f)
  karoubi_transformation : ∀ {A B : Diagram.{w, u, v} I} {Φ Ψ : Family A B}
      (hΦ : Φ.Coherent) (hΨ : Ψ.Coherent) (η : ∀ i, Φ.φ i ⟶ Ψ.φ i)
      (hη : Compatible η) (P : Idempotents.Karoubi (pair A).Obj),
    HEq (((Idempotents.functorExtension₂ _ _).map (transformation hΦ hΨ η hη)).app P).f
      ((descend Φ hΦ).map P.p ≫ (transformation hΦ hΨ η hη).app P.X ≫
        (descend Ψ hΨ).map P.p)
  karoubi_identity : ∀ A : Diagram.{w, u, v} I,
    (Idempotents.functorExtension₂ _ _).obj
      (descend (Family.identity A) (identity_coherent A)) =
        𝟭 (Idempotents.Karoubi (pair A).Obj)
  karoubi_composition : ∀ {A B C : Diagram.{w, u, v} I}
      (Φ : Family A B) (Θ : Family B C) (hΦ : Φ.Coherent) (hΘ : Θ.Coherent),
    (Idempotents.functorExtension₂ _ _).obj
      (descend (Φ.comp Θ) (composition_coherent Φ Θ hΦ hΘ)) =
        (Idempotents.functorExtension₂ _ _).obj (descend Φ hΦ) ⋙
          (Idempotents.functorExtension₂ _ _).obj (descend Θ hΘ)

/-- Coherent additive families and compatible transformations descend to common-stage pair
categories and their Karoubi envelopes.

Source: sketch 32, finite common-stage principle and coefficient categories; sketch 42,
Proposition `prop:pseudocone-functor` and Theorems `thm:pair-universal`,
`thm:karoubi-universal` (blueprint: lem-sbc-coherent-pair-functor-descent).

Proof plan (the node's fourteen steps):
1. Pentagon and naturality imply transitivity of associator-conjugated transport.
2. Additivity of the transitions makes transport additive; cancelling the middle
   associators shows that transport preserves identities and composition.
3. Finite coefficient composita supply common upper fields. Eventual equality is an
   equivalence relation, and the quotient Hom is the directed colimit of the stage Hom
   groups (def-weil-directed-colimit-abelian-groups, def-weil-size-convention).
4. Calculate identities, composites and the bilinearity equations over one common field;
   transitivity makes the results independent of representatives and the chosen field.
5. A stage zero object remains zero under an additive functor. Choose a common stage
   for two objects and use its biproduct inclusions and projections. Their equations hold
   in the quotient, so the pair categories have finite biproducts
   (def-weil-additive-category, def-weil-preadditive-category).
6. Evaluate the comparison tower at the two objects of a representative. Substitution
   and naturality of the comparison identify mapping a transported representative with
   transporting its mapped representative.
7. This gives quotient descent. At a common field the two comparison factors in a
   composite cancel, the unit comparison gives identities, and additivity is inherited
   from the stage functor (def-weil-pbc-additive-functor).
8. For a compatible transformation, rewrite its transported components using its
   comparison square. Stage naturality then proves naturality on each represented arrow.
9. Identity and vertically composed transformations have the indicated stage components;
   their compatibility squares compose. Thus all componentwise equations descend.
10. Whisker the comparisons to form a composite family. Expanding its tower, use the two
    original towers and naturality to obtain the composite tower. The identity tower is
    the diagram's associativity equation itself.
11. Expanding the representative formula shows that descent preserves composite functor
    families. At the identity stage, the same calculation gives the formulas for
    whiskering transformations, so equations involving whiskering also descend.
12. Use Mathlib's functorExtension₂: send an idempotent to its image under the descended
    functor and an arrow to its image. Functoriality preserves idempotence and the
    projector relation; additivity is inherited (def-weil-karoubi-envelope).
13. Naturality at the projector identifies the extension's component with the sandwiched
    component. The projector identities prove it is a Karoubi arrow, and naturality at
    an arbitrary Karoubi arrow proves its naturality.
14. Idempotence and naturality at the projector show that these extended components
    preserve identities and vertical composition. Functor composition has the same
    object, projector and arrow formulas, so it too is preserved.

The conclusion is one simultaneous existence statement, rather than choosing data from a
mere nonempty proposition. Every map and operation in that data has its canonical formula;
no additional hypothesis on the stages, their transitions or their functors is imposed. -/
theorem coherent_pair_functor_descent (l : ℕ) [Fact l.Prime]
    (K : Type w) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K] :
    Nonempty (DescentSystem.{w, u, v} (Padic.FiniteCoefficientFields l K)) := by
  sorry

end CategoryTheory.CommonStage
