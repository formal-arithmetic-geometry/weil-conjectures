/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.MarkedSchemeLifts
public import Sheaf.AlgebraicGeometry.ArtinRSTangentTensor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Proper marked scheme deformation classes and hulls

Source: Stacks Project, examples-defos.tex, Example 0DY7 and Tag 0ET5;
Formal Deformation Theory, Tags 06IX and 06JL
(blueprint: def-sfb-proper-scheme-deformation-data).
## Main definitions

- `reduction`.
- `Deformation`.
- `Classes`.
- `classOf`.
- `forget`.
- `IsBaseChange`.
- `ClassFunctor`.
- `Hull`.

-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProperSchemeDeformation
open ArtinDeformation
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The specified residue immersion. Source: Stacks 0DY7
(blueprint: def-sfb-proper-scheme-deformation-data). -/
def reduction (A : TestCategory k k) : Spec (.of k) ⟶ Spec (.of (ring A)) :=
  Spec.map (CommRingCat.ofHom (residue A).toRingHom)

/-- Proper objects of the existing category of marked flat lifts. Source: Stacks 0ET5
(blueprint: def-sfb-proper-scheme-deformation-data). -/
abbrev Deformation (A : TestCategory k k) :=
  ObjectProperty.FullSubcategory (fun Y : SchemeDeformation.Lift f (reduction A) ↦
    IsProper Y.projection)

/-- The actual marked isomorphism-class set. Source: Stacks 0ET5
(blueprint: def-sfb-proper-scheme-deformation-data). -/
def Classes (A : TestCategory k k) : Type (u + 1) :=
  Quot (fun Y Z : Deformation f A ↦ Nonempty (Y ≅ Z))

/-- Class of a marked proper deformation. Source: Stacks 0ET5
(blueprint: def-sfb-proper-scheme-deformation-data). -/
def classOf {A : TestCategory k k} (Y : Deformation f A) : Classes f A := Quot.mk _ Y

/-- Forget properness while retaining the marking. Source: Stacks 0ET5
(blueprint: def-sfb-proper-scheme-deformation-data). -/
def forget {A : TestCategory k k} : Classes f A →
    SchemeDeformation.Classes f (reduction A) :=
  Quot.map (fun Y ↦ Y.obj) (fun _ _ h ↦ h.map fun e ↦
    (ObjectProperty.ι _).mapIso e)

/-- The cartesian base-change relation on representatives. Source: Stacks 0DY7
(blueprint: def-sfb-proper-scheme-deformation-data). -/
def IsBaseChange {A B : TestCategory k k} (a : A ⟶ B)
    (Y : Deformation f A) (Z : Deformation f B) : Prop :=
  ∃ q : Z.obj.space ⟶ Y.obj.space,
    SchemeDeformation.IsBaseChange (Spec.map (CommRingCat.ofHom (map a).toRingHom))
      Y.obj Z.obj q

/-- A presentation of the actual class functor: the normalization specifies its value
on every cartesian base change, whose existence is required. Source: Stacks 0DY7
(blueprint: def-sfb-proper-scheme-deformation-data). -/
structure ClassFunctor where
  map : ∀ {A B : TestCategory k k}, (A ⟶ B) → Classes f A → Classes f B
  map_id : ∀ (A : TestCategory k k) (x : Classes f A), map (𝟙 A) x = x
  map_comp : ∀ {A B C : TestCategory k k} (a : A ⟶ B) (b : B ⟶ C)
    (x : Classes f A), map (a ≫ b) x = map b (map a x)
  exists_baseChange : ∀ {A B : TestCategory k k} (a : A ⟶ B) (Y : Deformation f A),
    ∃ Z : Deformation f B, IsBaseChange f a Y Z
  baseChange : ∀ {A B : TestCategory k k} (a : A ⟶ B)
    (Y : Deformation f A) (Z : Deformation f B),
    IsBaseChange f a Y Z → map a (classOf f Y) = classOf f Z

/-- A hull, with naturality, lifting over every surjection, and tangent bijectivity.
`LocalMap` is the recorded residue-preserving local algebra map. Such maps are
continuous: they take each maximal-ideal power into the corresponding power.
Source: Stacks 0ET5, 06IX and 06JL
(blueprint: def-sfb-proper-scheme-deformation-data). -/
structure Hull (F : ClassFunctor f) where
  algebra : CompleteLocalAlgebra k k
  eta : ∀ A : TestCategory k k, LocalMap algebra A → Classes f A
  naturality : ∀ {A B : TestCategory k k} (a : A ⟶ B)
    (x : LocalMap algebra A) (y : LocalMap algebra B),
    y.hom = (ArtinDeformation.map a).comp x.hom → F.map a (eta A x) = eta B y
  lifting : ∀ (A B : TestCategory k k) (q : B ⟶ A),
    Function.Surjective (ArtinDeformation.map q) →
    ∀ (a : LocalMap algebra A) (y : Classes f B), F.map q y = eta A a →
      ∃ b : LocalMap algebra B,
        (ArtinDeformation.map q).comp b.hom = a.hom ∧ eta B b = y
  tangent : Function.Bijective (eta (squareZeroTest (R := k) (k := k) k))

end AlgebraicGeometry.ProperSchemeDeformation
