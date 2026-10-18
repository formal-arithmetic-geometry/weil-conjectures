/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Coherent objects, topoi, and geometric morphisms

Source: Orgogozo, author draft, §8.1, printed pp. 17--18
(blueprint: def-trf-coherent-topos).
-/

@[expose] public section

universe w u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An object is quasi-compact when every epimorphic coproduct onto it has a
finite epimorphic sub-coproduct. Source: Orgogozo, §8.1
(blueprint: def-trf-coherent-topos). -/
def IsQuasiCompactObject {E : Type u} [Category.{v} E]
    [HasCoproducts.{w} E] (A : E) : Prop :=
  ∀ (I : Type w) (B : I → E) (f : ∀ i, B i ⟶ A),
    Epi (Sigma.desc f) →
      ∃ (s : Finset I), Epi (Sigma.desc (fun i : s ↦ f i.1))

/-- An object is quasi-separated when the fibre product of two quasi-compact
objects over it is quasi-compact. Source: Orgogozo, §8.1
(blueprint: def-trf-coherent-topos). -/
def IsQuasiSeparatedObject {E : Type u} [Category.{v} E]
    [HasCoproducts.{w} E] [HasFiniteLimits E] (A : E) : Prop :=
  ∀ (B C : E) (f : B ⟶ A) (g : C ⟶ A),
    IsQuasiCompactObject B → IsQuasiCompactObject C →
      ∀ (P : E) (p : P ⟶ B) (q : P ⟶ C),
        IsPullback p q f g → IsQuasiCompactObject P

/-- An object is coherent when it is both quasi-compact and quasi-separated.
Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsCoherentObject {E : Type u} [Category.{v} E]
    [HasCoproducts.{w} E] [HasFiniteLimits E] (A : E) : Prop :=
  IsQuasiCompactObject A ∧ IsQuasiSeparatedObject A

/-- A Grothendieck topos is coherent when it has a small generating full
subcategory of coherent objects closed under finite limits, including the
terminal object. Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsCoherentTopos (E : Type u) [Category.{v} E]
    [HasCoproducts.{w} E] [HasFiniteLimits E] : Prop :=
  IsGrothendieckTopos.{w} E ∧
    ∃ (G : Type w) (obj : G → E),
      (∀ (i : G), IsCoherentObject (obj i)) ∧
      (∀ (X : E),
        ∃ (I : Type w) (ι : I → G) (f : ∀ i, obj (ι i) ⟶ X),
          Epi (Sigma.desc f)) ∧
      ∀ (J : Type) [SmallCategory J] [FinCategory J],
        ObjectProperty.IsClosedUnderLimitsOfShape
          ((fun X : E => ∃ i, Nonempty (X ≅ obj i)) : ObjectProperty E) J

/-- A geometric morphism between coherent topoi is coherent when its inverse
image preserves coherent objects. Source: Orgogozo, §8.1
(blueprint: def-trf-coherent-topos). -/
def IsCoherentGeometricMorphism
    {E : Type u} {F : Type u'} [Category.{v} E] [Category.{v'} F]
    [HasCoproducts.{w} E] [HasCoproducts.{w} F]
    [HasFiniteLimits E] [HasFiniteLimits F]
    (_hE : IsCoherentTopos E) (_hF : IsCoherentTopos F)
    (u : GeometricMorphism E F) : Prop :=
  ∀ (X : F),
    IsCoherentObject X → IsCoherentObject (u.inverse.obj X)

/-- A geometric morphism is conservative when its inverse image reflects
isomorphisms. Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsConservativeGeometricMorphism
    {E : Type u} {F : Type u'} [Category.{v} E] [Category.{v'} F]
    [HasCoproducts.{w} E] [HasCoproducts.{w} F]
    [HasFiniteLimits E] [HasFiniteLimits F]
    (_hE : IsCoherentTopos E) (_hF : IsCoherentTopos F)
    (u : GeometricMorphism E F) : Prop :=
  u.inverse.ReflectsIsomorphisms

end CategoryTheory
