/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Composing sequences with varying coefficient categories

Source: Stacks Project, categories.tex, Tags 0030, 001B, 001I for the conventions;
the varying-category construction is the agent-formulated extraction in
lem-sf-compact-support-proper-image-tower, original proof Steps 1--3.
(blueprint: lem-sf-varying-coefficient-composite-sequences)

Index `n : ℕ` represents the positive level `n + 1`. The objects, arrows and functors
below have explicit data. Their compatibility and category/functor laws are proved levelwise.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB uC vC

namespace CategoryTheory
namespace CoefficientSequence

/-- A sequence with its transition in the next coefficient category.
Source: Stacks 0030, varying-level extension in the node's statement.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
structure Sequence (A : ℕ → Type uA) [∀ n, Category.{vA} (A n)]
    (S : ∀ n, A n ⥤ A (n + 1)) where
  obj : ∀ n, A n
  transition : ∀ n, obj (n + 1) ⟶ (S n).obj (obj n)

variable {A : ℕ → Type uA} [∀ n, Category.{vA} (A n)]
  {S : ∀ n, A n ⥤ A (n + 1)}

/-- Morphisms are levelwise maps satisfying the coefficient-transition square.
Source: Stacks 0030 and the node's varying-level convention.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
structure Hom (H K : Sequence A S) where
  app : ∀ n, H.obj n ⟶ K.obj n
  comm : ∀ n, H.transition n ≫ (S n).map (app n) = app (n + 1) ≫ K.transition n

private theorem hom_ext {H K : Sequence A S} {a b : Hom H K}
    (h : ∀ n, a.app n = b.app n) : a = b := by
  cases a with
  | mk app comm =>
    cases b with
    | mk app' comm' =>
      have : app = app' := funext h
      subst app'
      rfl

/-- Identity families satisfy the squares by preservation of identities and the unit laws.
Source: node proof Step 1; Stacks 001B, 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem identity_comm (H : Sequence A S) (n : ℕ) :
    H.transition n ≫ (S n).map (𝟙 (H.obj n)) = 𝟙 (H.obj (n + 1)) ≫ H.transition n := by
  simp

/-- Componentwise identity, with the square supplied by `identity_comm`.
Source: node proof Step 1; Stacks 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def homId (H : Sequence A S) : Hom H H where
  app n := 𝟙 (H.obj n)
  comm := identity_comm H

/-- Composite families satisfy the square: expand S(a ≫ b), use the square of a,
then that of b, and reassociate. Source: node proof Step 1; Stacks 001B, 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem composition_comm {H K L : Sequence A S} (a : Hom H K) (b : Hom K L) (n : ℕ) :
    H.transition n ≫ (S n).map (a.app n ≫ b.app n) =
      (a.app (n + 1) ≫ b.app (n + 1)) ≫ L.transition n := by
  rw [Functor.map_comp, ← Category.assoc, a.comm, Category.assoc, b.comm,
    ← Category.assoc]

/-- Componentwise composition of sequence morphisms.
Source: node proof Step 1; Stacks 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def homComp {H K L : Sequence A S} (a : Hom H K) (b : Hom K L) : Hom H L where
  app n := a.app n ≫ b.app n
  comm := composition_comm a b

/-- Left units hold at each level; equality of the families and proof irrelevance give
morphism equality. Source: node proof Step 1; Stacks 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem homId_comp {H K : Sequence A S} (a : Hom H K) : homComp (homId H) a = a := by
  apply hom_ext
  intro n
  exact Category.id_comp _

/-- Right units hold at each level; equality of the families and proof irrelevance give
morphism equality. Source: node proof Step 1; Stacks 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem homComp_id {H K : Sequence A S} (a : Hom H K) : homComp a (homId K) = a := by
  apply hom_ext
  intro n
  exact Category.comp_id _

/-- Associativity holds at each level; equality of the families and proof irrelevance give
morphism equality. Source: node proof Step 1; Stacks 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem homComp_assoc {H K L M : Sequence A S} (a : Hom H K) (b : Hom K L)
    (c : Hom L M) : homComp (homComp a b) c = homComp a (homComp b c) := by
  apply hom_ext
  intro n
  exact Category.assoc _ _ _

/-- The category with the specified componentwise operations.
Source: node proof Step 1; Stacks 0030.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
instance sequenceCategory : Category (Sequence A S) where
  Hom := Hom
  id := homId
  comp := homComp
  id_comp := homId_comp
  comp_id := homComp_id
  assoc := homComp_assoc

private theorem eqToHom_app {H K : Sequence A S} (h : H = K) (n : ℕ) :
    (eqToHom h : H ⟶ K).app n = eqToHom (congrArg (fun X ↦ X.obj n) h) := by
  subst h
  rfl

/-- For constant coefficients recover the recorded Mathlib inverse-system construction.
Source: Stacks 0030; `def-weil-inverse-system`; positive level n+1 is indexed by n.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def toInverseSystem {C : Type uA} [Category.{vA} C]
    (H : Sequence (fun _ : ℕ ↦ C) (fun _ ↦ 𝟭 C)) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence H.transition

variable {B : ℕ → Type uB} [∀ n, Category.{vB} (B n)]
  {T : ∀ n, B n ⥤ B (n + 1)}

/-- Transport a sequence by the specified functors and coefficient comparisons.
Source: node proof Step 2; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def mapObj (J : ∀ n, A n ⥤ B n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n) (H : Sequence A S) : Sequence B T where
  obj n := (J n).obj (H.obj n)
  transition n := (J (n + 1)).map (H.transition n) ≫ (e n).hom.app (H.obj n)

/-- Naturality of e moves J(S(a)) through e; the input square then gives the output
square, all in B(n+1). Source: node proof Step 2; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem map_comm (J : ∀ n, A n ⥤ B n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n)
    {H K : Sequence A S} (a : H ⟶ K) (n : ℕ) :
    (mapObj J e H).transition n ≫ (T n).map ((J n).map (a.app n)) =
      (J (n + 1)).map (a.app (n + 1)) ≫ (mapObj J e K).transition n := by
  change ((J (n + 1)).map (H.transition n) ≫ (e n).hom.app (H.obj n)) ≫
      (T n).map ((J n).map (a.app n)) =
    (J (n + 1)).map (a.app (n + 1)) ≫
      ((J (n + 1)).map (K.transition n) ≫ (e n).hom.app (K.obj n))
  have he := (e n).hom.naturality (a.app n)
  dsimp only [Functor.comp_map] at he
  rw [Category.assoc, ← he]
  change (J (n + 1)).map (H.transition n) ≫
      (J (n + 1)).map ((S n).map (a.app n)) ≫ (e n).hom.app (K.obj n) = _
  rw [← Category.assoc, ← Functor.map_comp, a.comm, Functor.map_comp, Category.assoc]

/-- The specified component maps, together with their naturality square.
Source: node proof Step 2; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def mapHom (J : ∀ n, A n ⥤ B n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n)
    {H K : Sequence A S} (a : H ⟶ K) : mapObj J e H ⟶ mapObj J e K where
  app n := (J n).map (a.app n)
  comm := map_comm J e a

/-- Functoriality on identities follows levelwise from J.map_id; proof fields are
irrelevant. Source: node proof Step 2; Stacks 001B.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem mapHom_id (J : ∀ n, A n ⥤ B n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n) (H : Sequence A S) :
    mapHom J e (𝟙 H) = 𝟙 (mapObj J e H) := by
  apply hom_ext
  intro n
  exact (J n).map_id _

/-- Functoriality on composites follows levelwise from J.map_comp; proof fields are
irrelevant. Source: node proof Step 2; Stacks 001B.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem mapHom_comp (J : ∀ n, A n ⥤ B n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n)
    {H K L : Sequence A S} (a : H ⟶ K) (b : K ⟶ L) :
    mapHom J e (a ≫ b) = mapHom J e a ≫ mapHom J e b := by
  apply hom_ext
  intro n
  exact (J n).map_comp _ _

/-- The sequence functor with the stated levels, transitions and maps.
Source: node proof Step 2; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def mapFunctor (J : ∀ n, A n ⥤ B n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n) : Sequence A S ⥤ Sequence B T where
  obj := mapObj J e
  map := mapHom J e
  map_id := mapHom_id J e
  map_comp := mapHom_comp J e

variable {C : ℕ → Type uC} [∀ n, Category.{vC} (C n)]
  {U : ∀ n, C n ⥤ C (n + 1)}

/-- The pasted coefficient comparison, using whiskering and functor associators.
Source: node proof Step 4; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
def paste (J : ∀ n, A n ⥤ B n) (D : ∀ n, B n ⥤ C n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n)
    (c : ∀ n, T n ⋙ D (n + 1) ≅ D n ⋙ U n) (n : ℕ) :
    S n ⋙ (J (n + 1) ⋙ D (n + 1)) ≅ (J n ⋙ D n) ⋙ U n :=
  (Functor.associator (S n) (J (n + 1)) (D (n + 1))).symm ≪≫
    Functor.isoWhiskerRight (e n) (D (n + 1)) ≪≫
    Functor.associator (J n) (T n) (D (n + 1)) ≪≫
    Functor.isoWhiskerLeft (J n) (c n) ≪≫ (Functor.associator (J n) (D n) (U n)).symm

/-- The pasted comparison has component c(J(H)) after D(e(H)). Expand the associators
(their components are identities) and whiskering, and cancel the unit factors.
Source: node proof Step 4; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem paste_app (J : ∀ n, A n ⥤ B n) (D : ∀ n, B n ⥤ C n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n)
    (c : ∀ n, T n ⋙ D (n + 1) ≅ D n ⋙ U n) (n : ℕ) (H : A n) :
    (paste J D e c n).hom.app H =
      (D (n + 1)).map ((e n).hom.app H) ≫ (c n).hom.app ((J n).obj H) := by
  simp [paste]

/-- A componentwise invertible morphism is invertible in the sequence category.
Multiply its square by the component inverses, using that S preserves inverse pairs.
These inverse components form an inverse family; both composites are identities levelwise.
Source: node proof Step 5; Stacks 001B, 001I.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem isIso_of_components {H K : Sequence A S} (a : H ⟶ K)
    (ha : ∀ n, IsIso (a.app n)) : IsIso a := by
  let b : K ⟶ H :=
    { app := fun n ↦ inv (a.app n)
      comm := by
        intro n
        apply (cancel_mono ((S n).map (a.app n))).1
        simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
          Functor.map_id, Category.comp_id]
        rw [a.comm, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp] }
  exact ⟨⟨b, by
    apply hom_ext
    intro n
    exact IsIso.hom_inv_id _, by
    apply hom_ext
    intro n
    exact IsIso.inv_hom_id _⟩⟩

/-- The explicit composite transition, the square for an arbitrary alpha, agreement with
the functor for the pasted comparison, and preservation of componentwise isomorphisms.
Source: Stacks 0030, 001B, 001I for conventions; node proof Steps 1--5.

Proof: Step 1 constructs the sequence categories using componentwise units and composition.
Step 2 applies naturality of e and c to construct the two functors with their displayed
transitions and component maps. Step 3 expands D.map_comp to obtain v, and uses naturality
of c followed by the input alpha square to get u ≫ S(b) = b(next) ≫ v. Step 4 pastes e and
c by whiskering, with inverse D(e.inv) after c.inv; the resulting functor has exactly the
same objects, transitions and maps as the composite. Step 5 inverts componentwise maps;
each level functor carries their inverse pairs to inverse pairs. All calculations take
place in one level category, with no common ambient category or strict derived lift.
(blueprint: lem-sf-varying-coefficient-composite-sequences) -/
theorem composite_spec
    (A : ℕ → Type uA) [∀ n, Category.{vA} (A n)]
    (B : ℕ → Type uB) [∀ n, Category.{vB} (B n)]
    (C : ℕ → Type uC) [∀ n, Category.{vC} (C n)]
    (S : ∀ n, A n ⥤ A (n + 1)) (T : ∀ n, B n ⥤ B (n + 1))
    (U : ∀ n, C n ⥤ C (n + 1))
    (J : ∀ n, A n ⥤ B n) (D : ∀ n, B n ⥤ C n)
    (e : ∀ n, S n ⋙ J (n + 1) ≅ J n ⋙ T n)
    (c : ∀ n, T n ⋙ D (n + 1) ≅ D n ⋙ U n) :
    (∀ (H : Sequence A S) (n : ℕ),
      ((mapFunctor J e ⋙ mapFunctor D c).obj H).transition n =
        (D (n + 1)).map ((J (n + 1)).map (H.transition n)) ≫
          (D (n + 1)).map ((e n).hom.app (H.obj n)) ≫
          (c n).hom.app ((J n).obj (H.obj n))) ∧
    (∀ (H : Sequence A S) (L : Sequence B T)
      (α : L ⟶ (mapFunctor J e).obj H) (n : ℕ),
      ((D (n + 1)).map (L.transition n) ≫ (c n).hom.app (L.obj n)) ≫
          (U n).map ((D n).map (α.app n)) =
        (D (n + 1)).map (α.app (n + 1)) ≫
          ((D (n + 1)).map ((J (n + 1)).map (H.transition n)) ≫
            (D (n + 1)).map ((e n).hom.app (H.obj n)) ≫
            (c n).hom.app ((J n).obj (H.obj n)))) ∧
    mapFunctor J e ⋙ mapFunctor D c =
      mapFunctor (fun n ↦ J n ⋙ D n) (paste J D e c) ∧
    (∀ (H K : Sequence A S) (a : H ⟶ K), (∀ n, IsIso (a.app n)) →
      ∀ n, IsIso (((mapFunctor J e).map a).app n)) ∧
    (∀ (L M : Sequence B T) (a : L ⟶ M), (∀ n, IsIso (a.app n)) →
      ∀ n, IsIso (((mapFunctor D c).map a).app n)) ∧
    (∀ (H K : Sequence A S) (a : H ⟶ K), (∀ n, IsIso (a.app n)) →
      ∀ n, IsIso (((mapFunctor J e ⋙ mapFunctor D c).map a).app n)) := by
  have htransition (H : Sequence A S) (n : ℕ) :
      ((mapFunctor J e ⋙ mapFunctor D c).obj H).transition n =
        (D (n + 1)).map ((J (n + 1)).map (H.transition n)) ≫
          (D (n + 1)).map ((e n).hom.app (H.obj n)) ≫
          (c n).hom.app ((J n).obj (H.obj n)) := by
    change (D (n + 1)).map (_ ≫ _) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
    rfl
  have hobj (H : Sequence A S) :
      (mapFunctor J e ⋙ mapFunctor D c).obj H =
        (mapFunctor (fun n ↦ J n ⋙ D n) (paste J D e c)).obj H := by
    change mapObj D c (mapObj J e H) =
      mapObj (fun n ↦ J n ⋙ D n) (paste J D e c) H
    dsimp only [mapObj]
    congr 1
    funext n
    simp only [Functor.comp_map, paste_app, Functor.map_comp, Category.assoc]
  refine ⟨htransition, ?_, ?_, ?_, ?_, ?_⟩
  · intro H L α n
    simpa only [mapObj, mapFunctor, Functor.map_comp, Category.assoc] using
      map_comm D c α n
  · refine Functor.ext hobj ?_
    intro H K a
    apply hom_ext
    intro n
    change (D n).map ((J n).map (a.app n)) =
      (eqToHom (hobj H)).app n ≫
        (D n).map ((J n).map (a.app n)) ≫ (eqToHom (hobj K).symm).app n
    rw [eqToHom_app, eqToHom_app]
    dsimp only [mapFunctor, mapObj, Functor.comp_obj]
    simp
  · intro H K a ha n
    change IsIso ((J n).map (a.app n))
    infer_instance
  · intro L M a ha n
    change IsIso ((D n).map (a.app n))
    infer_instance
  · intro H K a ha n
    change IsIso ((D n).map ((J n).map (a.app n)))
    infer_instance

end CoefficientSequence
end CategoryTheory
