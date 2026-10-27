/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Coherent systems of abelian sheaves on varying sites

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ,
lemma-colim-sites-injective, system data and morphisms; arbitrary small index category
(blueprint: def-per-varying-site-system).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A diagram of sites, with the specified coherent inverse-image identifications.
The inverse images are the actual left adjoints of continuous pushforward.
Source: Stacks Project, Tag 0EXZ, system data
(blueprint: def-per-varying-site-system). -/
structure VaryingSiteDiagram (I : Type u) [SmallCategory I] where
  site : I → Type u
  [category : ∀ i : I, SmallCategory (site i)]
  covering : ∀ i : I, Precoverage (site i)
  site_axioms : ∀ i : I, (covering i).IsSiteForCoverings
  functor : ∀ {j i : I}, (j ⟶ i) → site i ⥤ site j
  [continuous : ∀ {j i : I} (a : j ⟶ i),
    (functor a).IsContinuous (covering i).toGrothendieck (covering j).toGrothendieck]
  [set_exact : ∀ {j i : I} (a : j ⟶ i),
    PreservesFiniteLimits ((functor a).sheafPullback (Type u)
      (covering i).toGrothendieck (covering j).toGrothendieck)]
  [additive : ∀ {j i : I} (a : j ⟶ i),
    ((functor a).sheafPullback AddCommGrpCat.{u}
      (covering i).toGrothendieck (covering j).toGrothendieck).Additive]
  [exact_limits : ∀ {j i : I} (a : j ⟶ i),
    PreservesFiniteLimits ((functor a).sheafPullback AddCommGrpCat.{u}
      (covering i).toGrothendieck (covering j).toGrothendieck)]

attribute [instance] VaryingSiteDiagram.category VaryingSiteDiagram.continuous

variable {I : Type u} [SmallCategory I]

/-- Abelian sheaves at a vertex. Source: Stacks Project, Tag 0EXZ
(blueprint: def-per-varying-site-system). -/
abbrev VaryingSiteDiagram.Ab (D : VaryingSiteDiagram.{u} I) (i : I) :=
  Sheaf (D.covering i).toGrothendieck AddCommGrpCat.{u}

/-- The actual inverse-image functor of a transition morphism of sites.
Source: Stacks Project, Sites, Definition 00X1 and Tag 0EXZ
(blueprint: def-per-varying-site-system). -/
abbrev VaryingSiteDiagram.pull (D : VaryingSiteDiagram.{u} I)
    {j i : I} (a : j ⟶ i) : D.Ab i ⥤ D.Ab j :=
  (D.functor a).sheafPullback AddCommGrpCat.{u}
    (D.covering i).toGrothendieck (D.covering j).toGrothendieck

/-- Unit and composition identifications, with both unit laws and associativity.
Source: Stacks Project, Tag 0EXZ, cocycle convention
(blueprint: def-per-varying-site-system). -/
structure VaryingSiteCoherence (D : VaryingSiteDiagram.{u} I) where
  unit : ∀ i : I, D.pull (𝟙 i) ≅ 𝟭 (D.Ab i)
  comp : ∀ {k j i : I} (b : k ⟶ j) (a : j ⟶ i),
    D.pull (b ≫ a) ≅ D.pull a ⋙ D.pull b
  unit_left : ∀ {j i : I} (a : j ⟶ i) (A : D.Ab i),
    (comp (𝟙 j) a).hom.app A ≫ (unit j).hom.app ((D.pull a).obj A) =
      eqToHom (congrArg (fun t => (D.pull t).obj A) (Category.id_comp a))
  unit_right : ∀ {j i : I} (a : j ⟶ i) (A : D.Ab i),
    (comp a (𝟙 i)).hom.app A ≫ (D.pull a).map ((unit i).hom.app A) =
      eqToHom (congrArg (fun t => (D.pull t).obj A) (Category.comp_id a))
  associativity : ∀ {l k j i : I} (c : l ⟶ k) (b : k ⟶ j) (a : j ⟶ i)
    (A : D.Ab i),
    (comp (c ≫ b) a).hom.app A ≫ (comp c b).hom.app ((D.pull a).obj A) =
      eqToHom (congrArg (fun t => (D.pull t).obj A) (Category.assoc c b a)) ≫
        (comp c (b ≫ a)).hom.app A ≫ (D.pull c).map ((comp b a).hom.app A)

/-- A family with noninvertible inverse-image transitions obeying identity and cocycle.
Source: Stacks Project, Tag 0EXZ, system data
(blueprint: def-per-varying-site-system). -/
structure VaryingSiteSystem (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) where
  obj : ∀ i : I, D.Ab i
  transition : ∀ {j i : I} (a : j ⟶ i), (D.pull a).obj (obj i) ⟶ obj j
  identity : ∀ i : I, transition (𝟙 i) = (e.unit i).hom.app (obj i)
  cocycle : ∀ {k j i : I} (b : k ⟶ j) (a : j ⟶ i),
    transition (b ≫ a) = (e.comp b a).hom.app (obj i) ≫
      (D.pull b).map (transition a) ≫ transition b

variable {D : VaryingSiteDiagram.{u} I} {e : VaryingSiteCoherence D}

/-- Compatible component maps. Source: Stacks Project, Tag 0EXZ, maps of systems
(blueprint: def-per-varying-site-system). -/
def VaryingSiteSystem.Hom (F G : VaryingSiteSystem D e) :=
  {h : ∀ i : I, F.obj i ⟶ G.obj i // ∀ {j i : I} (a : j ⟶ i),
    (D.pull a).map (h i) ≫ G.transition a = F.transition a ≫ h j}

/-- Component identities commute with transitions.
Source: Stacks Project, Tag 0EXZ (blueprint: def-per-varying-site-system).
Proof: preservation of identities and the identity laws in each sheaf category
reduce both sides to the transition. -/
theorem varyingSiteSystem_identity_compatible (F : VaryingSiteSystem D e)
    {j i : I} (a : j ⟶ i) :
    (D.pull a).map (𝟙 (F.obj i)) ≫ F.transition a = F.transition a ≫ 𝟙 (F.obj j) := by
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]

/-- Component composites commute with transitions.
Source: Stacks Project, Tag 0EXZ (blueprint: def-per-varying-site-system).
Proof: expand preservation of composition, substitute the two compatibility
squares and reassociate. -/
theorem varyingSiteSystem_composition_compatible
    {F G H : VaryingSiteSystem D e} (f : F.Hom G) (g : G.Hom H)
    {j i : I} (a : j ⟶ i) :
    (D.pull a).map (f.val i ≫ g.val i) ≫ H.transition a =
      F.transition a ≫ (f.val j ≫ g.val j) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [g.property a, ← Category.assoc, f.property a, Category.assoc]

/-- Componentwise identity and composition.
Source: Stacks Project, Tag 0EXZ (blueprint: def-per-varying-site-system). -/
instance varyingSiteSystemCategoryStruct : CategoryStruct (VaryingSiteSystem D e) where
  Hom F G := F.Hom G
  id F := ⟨fun i => 𝟙 (F.obj i), varyingSiteSystem_identity_compatible F⟩
  comp f g := ⟨fun i => f.val i ≫ g.val i, varyingSiteSystem_composition_compatible f g⟩

/-- The component operations obey the category laws.
Source: Stacks Project, Tag 0EXZ (blueprint: def-per-varying-site-system).
Proof: equality of compatible families is equality of their components by subtype
extensionality; each equation is the corresponding sheaf-category equation. -/
theorem varyingSiteSystem_category_laws :
    (∀ (F G : VaryingSiteSystem D e) (f : F ⟶ G), 𝟙 F ≫ f = f ∧ f ≫ 𝟙 G = f) ∧
    (∀ (F G H K : VaryingSiteSystem D e) (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ K),
      (f ≫ g) ≫ h = f ≫ (g ≫ h)) := by
  constructor
  · intro F G f
    constructor
    · exact Subtype.ext (funext (fun i ↦ Category.id_comp (f.val i)))
    · exact Subtype.ext (funext (fun i ↦ Category.comp_id (f.val i)))
  · intro F G H K f g h
    exact Subtype.ext (funext (fun i ↦ Category.assoc (f.val i) (g.val i) (h.val i)))

/-- The category of coherent systems, with the prescribed componentwise operations.
Source: Stacks Project, Tag 0EXZ (blueprint: def-per-varying-site-system). -/
instance varyingSiteSystemCategory : Category (VaryingSiteSystem D e) where
  id_comp f := (varyingSiteSystem_category_laws.1 _ _ f).1
  comp_id f := (varyingSiteSystem_category_laws.1 _ _ f).2
  assoc f g h := varyingSiteSystem_category_laws.2 _ _ _ _ f g h

/-- Evaluation is the component functor on objects and arrows.
Source: Stacks Project, Tag 0EXZ (blueprint: def-per-varying-site-system). -/
def VaryingSiteSystem.evaluation (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) (i : I) : VaryingSiteSystem D e ⥤ D.Ab i where
  obj F := F.obj i
  map h := h.val i

end CategoryTheory
