module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Whiskering

/-! # Pseudococones on strict category diagrams

Source: the coherent families in the finite-representative extension of Stacks Project,
Categories, Tag 04AX (blueprint: def-per-strict-diagram-pseudococones).
The comparison maps point from the later-stage restriction to the earlier-stage functor.
-/

@[expose] public section

universe z u v u' v'

namespace CategoryTheory

open Limits CategoryTheory.Functor

/-- A family of functors with invertible, normalized and coherent transition comparisons.
Source: the coherent-family extension of Stacks Tag 04AX
(blueprint: def-per-strict-diagram-pseudococones). -/
structure StrictDiagramPseudococone {J : Type z} [SmallCategory J]
    (D : J ⥤ Cat.{z, z}) (A : Type u) [Category.{v} A] where
  functor : ∀ j : J, D.obj j ⥤ A
  comparison : ∀ {j k : J} (a : j ⟶ k), (D.map a).toFunctor ⋙ functor k ≅ functor j
  identity : ∀ (j : J) (x : D.obj j), (comparison (𝟙 j)).hom.app x =
    (functor j).map (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_id j)))
  composition : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l) (x : D.obj j),
    (comparison (a ≫ b)).hom.app x =
      (functor l).map (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_comp a b))) ≫
        (comparison b).hom.app ((D.map a).toFunctor.obj x) ≫ (comparison a).hom.app x

namespace StrictDiagramPseudococone

variable {J : Type z} [SmallCategory J] {D : J ⥤ Cat.{z, z}}
variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- Modifications are compatible families of natural transformations.
Source: coherent-family extension of Stacks Tag 04AX
(blueprint: def-per-strict-diagram-pseudococones). -/
structure Hom (P Q : StrictDiagramPseudococone D A) where
  app : ∀ j : J, P.functor j ⟶ Q.functor j
  compatibility : ∀ {j k : J} (a : j ⟶ k) (x : D.obj j),
    (P.comparison a).hom.app x ≫ (app j).app x =
      (app k).app ((D.map a).toFunctor.obj x) ≫ (Q.comparison a).hom.app x

/-- Modification equality is componentwise equality.
Source: Stacks Tag 04AX, coherent-family extension
(blueprint: def-per-strict-diagram-pseudococones).
Proof: the compatibility fields are propositions, and the transformation family is all the data. -/
theorem hom_ext {P Q : StrictDiagramPseudococone D A} {f g : Hom P Q}
    (h : ∀ j : J, f.app j = g.app j) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have : f = g := funext h
      subst g
      rfl

/-- Identity families satisfy the modification square.
Source: Stacks Tag 04AX, coherent-family extension
(blueprint: def-per-strict-diagram-pseudococones).
Proof: both sides reduce to the comparison component by the identity laws. -/
theorem identity_compatible (P : StrictDiagramPseudococone D A)
    {j k : J} (a : j ⟶ k) (x : D.obj j) :
    (P.comparison a).hom.app x ≫ (NatTrans.id (P.functor j)).app x =
      (NatTrans.id (P.functor k)).app ((D.map a).toFunctor.obj x) ≫
        (P.comparison a).hom.app x := by
  simp

/-- Modification squares compose vertically.
Source: Stacks Tag 04AX, coherent-family extension
(blueprint: def-per-strict-diagram-pseudococones).
Proof: associate the three factors, apply the square for the first modification and then
that for the second, and reassociate. -/
theorem composition_compatible {P Q R : StrictDiagramPseudococone D A}
    (f : Hom P Q) (g : Hom Q R) {j k : J} (a : j ⟶ k) (x : D.obj j) :
    (P.comparison a).hom.app x ≫ ((f.app j) ≫ (g.app j)).app x =
      ((f.app k) ≫ (g.app k)).app ((D.map a).toFunctor.obj x) ≫
        (R.comparison a).hom.app x := by
  change (P.comparison a).hom.app x ≫ ((f.app j).app x ≫ (g.app j).app x) =
    ((f.app k).app ((D.map a).toFunctor.obj x) ≫
      (g.app k).app ((D.map a).toFunctor.obj x)) ≫ (R.comparison a).hom.app x
  rw [← Category.assoc, f.compatibility a x, Category.assoc,
    g.compatibility a x, ← Category.assoc]

/-- The category of pseudococones, with componentwise identities and composition.
Source: Stacks Tag 04AX, coherent-family extension
(blueprint: def-per-strict-diagram-pseudococones). -/
@[implicit_reducible] instance category : Category (StrictDiagramPseudococone D A) where
  Hom := Hom
  id P := ⟨fun j ↦ 𝟙 (P.functor j), identity_compatible P⟩
  comp f g := ⟨fun j ↦ f.app j ≫ g.app j, composition_compatible f g⟩
  id_comp f := hom_ext (fun j ↦ Category.id_comp (f.app j))
  comp_id f := hom_ext (fun j ↦ Category.comp_id (f.app j))
  assoc f g h := hom_ext (fun j ↦ Category.assoc (f.app j) (g.app j) (h.app j))

/-- The equality comparisons of a restricted functor are normalized and coherent.
Source: Stacks Tag 04AX, coherent-family extension
(blueprint: def-per-strict-diagram-pseudococones).
Proof: equality-to-isomorphism respects identities and composition. Apply the cocone equations
and functoriality of the restricted functor; equality proofs are propositionally unique. -/
theorem restriction_coherence (c : Cocone D) (F : c.pt ⥤ A) :
    (∀ (j : J) (x : D.obj j),
      (Functor.isoWhiskerRight (eqToIso (congrArg Cat.Hom.toFunctor (c.w (𝟙 j)))) F).hom.app x =
        ((c.ι.app j).toFunctor ⋙ F).map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_id j)))) ∧
    (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l) (x : D.obj j),
      (Functor.isoWhiskerRight (eqToIso (congrArg Cat.Hom.toFunctor (c.w (a ≫ b)))) F).hom.app x =
        ((c.ι.app l).toFunctor ⋙ F).map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_comp a b))) ≫
        (Functor.isoWhiskerRight (eqToIso (congrArg Cat.Hom.toFunctor (c.w b))) F).hom.app
          ((D.map a).toFunctor.obj x) ≫
        (Functor.isoWhiskerRight (eqToIso (congrArg Cat.Hom.toFunctor (c.w a))) F).hom.app x) := by
  constructor
  · intro j x
    simp [eqToHom_map]
  · intro j k l a b x
    simp [eqToHom_map]

/-- Restriction has the identity comparisons supplied by the strict cocone equations.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones). -/
def restrictObj (c : Cocone D) (F : c.pt ⥤ A) : StrictDiagramPseudococone D A where
  functor j := (c.ι.app j).toFunctor ⋙ F
  comparison a := Functor.isoWhiskerRight (eqToIso (congrArg Cat.Hom.toFunctor (c.w a))) F
  identity := (restriction_coherence c F).1
  composition := (restriction_coherence c F).2

/-- Restriction of a natural transformation is compatible with equality comparisons.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones).
Proof: apply naturality to the equality morphism expressing the cocone equation. -/
theorem restriction_compatible (c : Cocone D) {F G : c.pt ⥤ A} (f : F ⟶ G)
    {j k : J} (a : j ⟶ k) (x : D.obj j) :
    ((restrictObj c F).comparison a).hom.app x ≫
        (whiskerLeft (c.ι.app j).toFunctor f).app x =
      (whiskerLeft (c.ι.app k).toFunctor f).app ((D.map a).toFunctor.obj x) ≫
        ((restrictObj c G).comparison a).hom.app x := by
  change F.map ((eqToHom (congrArg Cat.Hom.toFunctor (c.w a))).app x) ≫
      f.app ((c.ι.app j).toFunctor.obj x) =
    f.app ((c.ι.app k).toFunctor.obj ((D.map a).toFunctor.obj x)) ≫
      G.map ((eqToHom (congrArg Cat.Hom.toFunctor (c.w a))).app x)
  exact f.naturality _

/-- The canonical restriction functor, including its action on transformations.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones). -/
def restriction (c : Cocone D) (A : Type u) [Category.{v} A] :
    (c.pt ⥤ A) ⥤ StrictDiagramPseudococone D A where
  obj := restrictObj c
  map f := ⟨fun j ↦ whiskerLeft (c.ι.app j).toFunctor f, restriction_compatible c f⟩
  map_id F := hom_ext (fun j ↦ ((whiskeringLeft _ _ A).obj
    (c.ι.app j).toFunctor).map_id F)
  map_comp f g := hom_ext (fun j ↦ ((whiskeringLeft _ _ A).obj
    (c.ι.app j).toFunctor).map_comp f g)

/-- Postcomposition preserves the two coherence equations.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones).
Proof: apply the postcomposing functor to the two equations, then use its preservation
of identities, composition, and equality morphisms. -/
theorem postcompose_coherence (P : StrictDiagramPseudococone D A) (H : A ⥤ B) :
    (∀ (j : J) (x : D.obj j),
      (Functor.isoWhiskerRight (P.comparison (𝟙 j)) H).hom.app x =
        (P.functor j ⋙ H).map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_id j)))) ∧
    (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l) (x : D.obj j),
      (Functor.isoWhiskerRight (P.comparison (a ≫ b)) H).hom.app x =
        (P.functor l ⋙ H).map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) (D.map_comp a b))) ≫
        (Functor.isoWhiskerRight (P.comparison b) H).hom.app ((D.map a).toFunctor.obj x) ≫
        (Functor.isoWhiskerRight (P.comparison a) H).hom.app x) := by
  constructor
  · intro j x
    change H.map ((P.comparison (𝟙 j)).hom.app x) = _
    rw [P.identity]
    rfl
  · intro j k l a b x
    change H.map ((P.comparison (a ≫ b)).hom.app x) = _
    rw [P.composition, H.map_comp, H.map_comp]
    rfl

/-- Postcomposition on pseudococone objects.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones). -/
def postcomposeObj (H : A ⥤ B) (P : StrictDiagramPseudococone D A) :
    StrictDiagramPseudococone D B where
  functor j := P.functor j ⋙ H
  comparison a := Functor.isoWhiskerRight (P.comparison a) H
  identity := (postcompose_coherence P H).1
  composition := (postcompose_coherence P H).2

/-- Postcomposition preserves modification squares.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones).
Proof: apply the functor to a modification square and expand preservation of composition. -/
theorem postcompose_compatible (H : A ⥤ B) {P Q : StrictDiagramPseudococone D A}
    (f : P ⟶ Q) {j k : J} (a : j ⟶ k) (x : D.obj j) :
    ((postcomposeObj H P).comparison a).hom.app x ≫ (whiskerRight (f.app j) H).app x =
      (whiskerRight (f.app k) H).app ((D.map a).toFunctor.obj x) ≫
        ((postcomposeObj H Q).comparison a).hom.app x := by
  change H.map ((P.comparison a).hom.app x) ≫ H.map ((f.app j).app x) =
    H.map ((f.app k).app ((D.map a).toFunctor.obj x)) ≫
      H.map ((Q.comparison a).hom.app x)
  simpa only [H.map_comp] using congrArg H.map (f.compatibility a x)

/-- Postcomposition on pseudococones and modifications.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones). -/
def postcompose (H : A ⥤ B) :
    StrictDiagramPseudococone D A ⥤ StrictDiagramPseudococone D B where
  obj := postcomposeObj H
  map f := ⟨fun j ↦ whiskerRight (f.app j) H, postcompose_compatible H f⟩
  map_id P := hom_ext (fun j ↦ ((whiskeringRight _ A B).obj H).map_id (P.functor j))
  map_comp f g := hom_ext (fun j ↦ ((whiskeringRight _ A B).obj H).map_comp
    (f.app j) (g.app j))

/-- A transformation of postcomposing functors gives a modification at every pseudococone.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones).
Proof: its square is naturality of the given transformation at the comparison component. -/
theorem postcompose_transformation_compatible {H H' : A ⥤ B} (t : H ⟶ H')
    (P : StrictDiagramPseudococone D A) {j k : J} (a : j ⟶ k) (x : D.obj j) :
    ((postcomposeObj H P).comparison a).hom.app x ≫
        (whiskerLeft (P.functor j) t).app x =
      (whiskerLeft (P.functor k) t).app ((D.map a).toFunctor.obj x) ≫
        ((postcomposeObj H' P).comparison a).hom.app x := by
  exact t.naturality ((P.comparison a).hom.app x)

/-- The modification construction is natural in the pseudococone.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones).
Proof: componentwise this is naturality of the transformation at each modification component. -/
theorem postcompose_transformation_naturality {H H' : A ⥤ B} (t : H ⟶ H')
    {P Q : StrictDiagramPseudococone D A} (f : P ⟶ Q) :
    (postcompose H).map f ≫
        (⟨fun j ↦ whiskerLeft (Q.functor j) t,
          postcompose_transformation_compatible t Q⟩ : postcomposeObj H Q ⟶ postcomposeObj H' Q) =
      (⟨fun j ↦ whiskerLeft (P.functor j) t,
          postcompose_transformation_compatible t P⟩ : postcomposeObj H P ⟶ postcomposeObj H' P) ≫
        (postcompose H').map f := by
  apply hom_ext
  intro j
  apply NatTrans.ext
  funext x
  exact t.naturality ((f.app j).app x)

/-- The natural transformation induced by a transformation of postcomposing functors.
Source: Stacks Tag 04AX (blueprint: def-per-strict-diagram-pseudococones). -/
def postcomposeMap {H H' : A ⥤ B} (t : H ⟶ H') :
    postcompose (D := D) H ⟶ postcompose H' where
  app P := ⟨fun j ↦ whiskerLeft (P.functor j) t,
    postcompose_transformation_compatible t P⟩
  naturality _ _ f := postcompose_transformation_naturality t f

/-- Reindexing preserves the identity and composition coherence equations.
Source: Stacks Tags 04AX and 04E7 (blueprint: def-per-strict-diagram-pseudococones).
Proof: use preservation of identity and composition by the index functor, then the original
pseudococone equations. Equality-to-morphism respects those equalities. -/
theorem reindex_coherence {K : Type z} [SmallCategory K] (w : K ⥤ J)
    (P : StrictDiagramPseudococone D A) :
    (∀ (k : K) (x : D.obj (w.obj k)),
      (P.comparison (w.map (𝟙 k))).hom.app x =
        (P.functor (w.obj k)).map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) ((w ⋙ D).map_id k)))) ∧
    (∀ {i j k : K} (a : i ⟶ j) (b : j ⟶ k) (x : D.obj (w.obj i)),
      (P.comparison (w.map (a ≫ b))).hom.app x =
        (P.functor (w.obj k)).map
          (eqToHom (congrArg (fun f ↦ f.toFunctor.obj x) ((w ⋙ D).map_comp a b))) ≫
        (P.comparison (w.map b)).hom.app ((D.map (w.map a)).toFunctor.obj x) ≫
        (P.comparison (w.map a)).hom.app x) := by
  have identity_of_eq (j : J) (a : j ⟶ j) (ha : a = 𝟙 j) (x : D.obj j)
      (e : (D.map a).toFunctor.obj x = x) :
      (P.comparison a).hom.app x = (P.functor j).map (eqToHom e) := by
    subst a
    exact P.identity j x
  have composition_of_eq {i j k : J} (a : i ⟶ j) (b : j ⟶ k) (c : i ⟶ k)
      (hc : c = a ≫ b) (x : D.obj i)
      (e : (D.map c).toFunctor.obj x =
        (D.map b).toFunctor.obj ((D.map a).toFunctor.obj x)) :
      (P.comparison c).hom.app x = (P.functor k).map (eqToHom e) ≫
        (P.comparison b).hom.app ((D.map a).toFunctor.obj x) ≫
        (P.comparison a).hom.app x := by
    subst c
    exact P.composition a b x
  constructor
  · intro k x
    exact identity_of_eq (w.obj k) (w.map (𝟙 k)) (w.map_id k) x
      (congrArg (fun f ↦ f.toFunctor.obj x) ((w ⋙ D).map_id k))
  · intro i j k a b x
    exact composition_of_eq (w.map a) (w.map b) (w.map (a ≫ b)) (w.map_comp a b) x
      (congrArg (fun f ↦ f.toFunctor.obj x) ((w ⋙ D).map_comp a b))

/-- Reindexing on pseudococone objects.
Source: Stacks Tags 04AX and 04E7 (blueprint: def-per-strict-diagram-pseudococones). -/
def reindexObj {K : Type z} [SmallCategory K] (w : K ⥤ J)
    (P : StrictDiagramPseudococone D A) : StrictDiagramPseudococone (w ⋙ D) A where
  functor k := P.functor (w.obj k)
  comparison a := P.comparison (w.map a)
  identity := (reindex_coherence w P).1
  composition := (reindex_coherence w P).2

/-- Restricting the index family, on both objects and modifications.
Source: Stacks Tags 04AX and 04E7 (blueprint: def-per-strict-diagram-pseudococones). -/
def reindex {K : Type z} [SmallCategory K] (w : K ⥤ J) :
    StrictDiagramPseudococone D A ⥤ StrictDiagramPseudococone (w ⋙ D) A where
  obj := reindexObj w
  map f := ⟨fun k ↦ f.app (w.obj k), fun a x ↦ f.compatibility (w.map a) x⟩
  map_id _ := hom_ext (fun _ ↦ rfl)
  map_comp _ _ := hom_ext (fun _ ↦ rfl)

end StrictDiagramPseudococone
end CategoryTheory
