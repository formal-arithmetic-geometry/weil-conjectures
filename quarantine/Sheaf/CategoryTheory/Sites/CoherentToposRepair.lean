/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Sheaf.Paper.OrientedNearbyCycles

/-!
# Universe packaged coherent-topos predicates

Source: Orgogozo, author draft, §8.1, printed pp. 17--18
(blueprint: def-trf-coherent-topos).

The original predicates in `CategoryTheory.Sites.CoherentTopos` take
`HasCoproducts` as an ambient instance.  A sheaf category in the size convention
has the required structure, but typeclass search cannot infer its large
coproduct universe from a bare occurrence of the predicate.  These predicates
package the coproduct structures existentially, preserving the same mathematical
notion while making the interface usable for the vanishing topoi.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe w u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CoherentToposRepair

/-- Coherence of a topos with its coproduct structure packaged as data.
Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsCoherentTopos (E : Type u) [Category.{v} E] : Prop :=
  ∃ h : HasCoproducts.{w, v, u} E,
    ∃ hL : HasFiniteLimits.{v, u} E,
      @CategoryTheory.IsCoherentTopos.{w, u, v} E _ h hL

/-- Coherence of a geometric morphism, packaging the coproduct structures used by
its source and target coherent-topos predicates.
Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsCoherentGeometricMorphism
    {E : Type u} {F : Type u'} [Category.{v} E] [Category.{v'} F]
    (_hE : IsCoherentTopos.{w, u, v} E) (_hF : IsCoherentTopos.{w, u', v'} F)
    (u : GeometricMorphism E F) : Prop :=
  ∃ hE : HasCoproducts.{w, v, u} E,
    ∃ hF : HasCoproducts.{w, v', u'} F,
      ∃ hLE : HasFiniteLimits.{v, u} E,
        ∃ hLF : HasFiniteLimits.{v', u'} F,
          @CategoryTheory.IsCoherentGeometricMorphism.{w, u, v, u', v'}
            E F _ _ hE hF hLE hLF
            (Classical.choose_spec (Classical.choose_spec _hE))
            (Classical.choose_spec (Classical.choose_spec _hF)) u

/-- Conservativity of a geometric morphism, with the same packaged coherent-topos
structures as `IsCoherentGeometricMorphism`.
Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsConservativeGeometricMorphism
    {E : Type u} {F : Type u'} [Category.{v} E] [Category.{v'} F]
    (_hE : IsCoherentTopos.{w, u, v} E) (_hF : IsCoherentTopos.{w, u', v'} F)
    (u : GeometricMorphism E F) : Prop :=
  ∃ hE : HasCoproducts.{w, v, u} E,
    ∃ hF : HasCoproducts.{w, v', u'} F,
      ∃ hLE : HasFiniteLimits.{v, u} E,
        ∃ hLF : HasFiniteLimits.{v', u'} F,
          @CategoryTheory.IsConservativeGeometricMorphism.{w, u, v, u', v'}
            E F _ _ hE hF hLE hLF
            (Classical.choose_spec (Classical.choose_spec _hE))
            (Classical.choose_spec (Classical.choose_spec _hF)) u

/-- The packaged coherent-topos predicate for an oriented-nearby-cycles vanishing topos.
Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsCoherentVanishingTopos {T B : AlgebraicGeometry.Scheme.{u}}
    (f : T ⟶ B) : Prop :=
  IsCoherentTopos.{max (u + 1) v, max (max (u + 2) (v + 1)) (u + 1) v,
    max (u + 1) v} (AlgebraicGeometry.OrientedNearbyCycles.VanishingTopos.{u, v} f)

/-- Coherence of the canonical square morphism between vanishing topoi, with packaged
size structures. Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsCoherentVanishingSquare {T' B' T B : AlgebraicGeometry.Scheme.{u}}
    (f : T ⟶ B) (f' : T' ⟶ B') (h : T' ⟶ T) (g : B' ⟶ B)
    (comm : h ≫ f = f' ≫ g) : Prop :=
  ∃ hE : IsCoherentVanishingTopos.{u, v} f',
    ∃ hF : IsCoherentVanishingTopos.{u, v} f,
      IsCoherentGeometricMorphism.{max (u + 1) v,
        max (max (u + 2) (v + 1)) (u + 1) v, max (u + 1) v,
        max (max (u + 2) (v + 1)) (u + 1) v, max (u + 1) v}
        hE hF (AlgebraicGeometry.OrientedNearbyCycles.squareMorphism f f' h g comm)

/-- Conservativity of the canonical square morphism between vanishing topoi, with
packaged size structures. Source: Orgogozo, §8.1 (blueprint: def-trf-coherent-topos). -/
def IsConservativeVanishingSquare {T' B' T B : AlgebraicGeometry.Scheme.{u}}
    (f : T ⟶ B) (f' : T' ⟶ B') (h : T' ⟶ T) (g : B' ⟶ B)
    (comm : h ≫ f = f' ≫ g) : Prop :=
  ∃ hE : IsCoherentVanishingTopos.{u, v} f',
    ∃ hF : IsCoherentVanishingTopos.{u, v} f,
      IsConservativeGeometricMorphism.{max (u + 1) v,
        max (max (u + 2) (v + 1)) (u + 1) v, max (u + 1) v,
        max (max (u + 2) (v + 1)) (u + 1) v, max (u + 1) v}
        hE hF (AlgebraicGeometry.OrientedNearbyCycles.squareMorphism f f' h g comm)

end CategoryTheory.CoherentToposRepair
