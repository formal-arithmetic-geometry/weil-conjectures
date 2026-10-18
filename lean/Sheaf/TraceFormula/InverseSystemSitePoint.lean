/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Inverse-system site points

Source: Stacks Project, Sites, Tags 00YC and 00YA, with the inverse-system
construction in Tag 00YQ (blueprint: lem-trf-inverse-system-site-point).

The inverse system is represented by a functor from the opposite of a directed
poset.  Its colimit of representables is the functor `inverseSystemHomFunctor`,
and the colimit of sections along it is the functor
`inverseSystemSectionColimitFunctor`.  The site is a precoverage satisfying the
site axioms `Precoverage.IsSiteForCoverings`, with sheaves for the generated
Grothendieck topology, as in the dependency def-weil-pbc-sites-and-cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The opposite-category diagram of objects in an inverse system.
Source: Stacks Project, Sites, Tag 00YQ (blueprint: lem-trf-inverse-system-site-point). -/
def inverseSystemOppositeDiagram {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) : I ⥤ Cᵒᵖ where
  obj i := op (U.obj (op i))
  map {X Y} f := (U.map f.op).op
  map_id i := by simp
  map_comp f g := by simp

/-- The diagram of representable functors obtained from an inverse system.
Source: Stacks Project, Sites, Tags 00YC and 00YQ
(blueprint: lem-trf-inverse-system-site-point). -/
def inverseSystemRepresentableDiagram {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) : I ⥤ (C ⥤ Type u) where
  obj i := coyoneda.obj (op (U.obj (op i)))
  map {X Y} f := coyoneda.map (U.map f.op).op
  map_id i := by simp
  map_comp f g := by simp

/-- The colimit of representables attached to an inverse system,
`u(W) = colim_i Hom(U_i, W)`.
Source: Stacks Project, Sites, Tags 00YC and 00YQ
(blueprint: lem-trf-inverse-system-site-point). -/
noncomputable def inverseSystemHomFunctor {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (U : Iᵒᵖ ⥤ C) : C ⥤ Type u :=
  colimit (inverseSystemRepresentableDiagram U)

/-- The section diagram `i ↦ F(U_i)` of a sheaf along an inverse system.
Source: Stacks Project, Sites, Tags 00YA and 00YQ
(blueprint: lem-trf-inverse-system-site-point). -/
def inverseSystemSectionDiagram {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] {J : GrothendieckTopology C}
    (U : Iᵒᵖ ⥤ C) (F : Sheaf J (Type w)) : I ⥤ Type w :=
  inverseSystemOppositeDiagram U ⋙ ObjectProperty.FullSubcategory.obj F

/-- The functor `F ↦ colim_i F(U_i)` on sheaves of sets, acting on a morphism of
sheaves by its section maps at the `U_i`; its value at `F` is the colimit of
`inverseSystemSectionDiagram U F`.
Source: Stacks Project, Sites, Tags 00YA and 00YQ
(blueprint: lem-trf-inverse-system-site-point). -/
noncomputable def inverseSystemSectionColimitFunctor {C : Type u} [Category.{u} C]
    {I : Type u} [PartialOrder I] (J : GrothendieckTopology C) (U : Iᵒᵖ ⥤ C) :
    Sheaf J (Type (max u w)) ⥤ Type (max u w) :=
  sheafToPresheaf J (Type (max u w)) ⋙
    (Functor.whiskeringLeft I Cᵒᵖ (Type (max u w))).obj (inverseSystemOppositeDiagram U) ⋙
      colim

/-- Inverse-system criterion for a point of a small site.
Source: Stacks Project, Sites, Tags 00YC (Proposition proposition-point-limits),
00YA (Lemma lemma-point-site-topos), and 00YQ (Proposition proposition-criterion-points)
(blueprint: lem-trf-inverse-system-site-point).

Proof sketch (the node's steps):
1. A directed colimit of sets is the quotient of the pairs `(i, a)` by eventual
   equality at a common later index; every class has a representative.
2. `u(h)[i, a] = [i, h ∘ a]` is a functor; `Hom(U_i, -)` preserves finite limits and
   filtered colimits commute with finite limits in sets, so `u` preserves finite limits.
3. `S(F) = colim_i F(U_i)` preserves finite limits: finite limits of sheaves are
   computed sectionwise, and the same commutation applies.
4. The covering hypothesis is joint surjectivity; an empty covering forces `u(W)` empty.
5. The neighbourhood stalk `T(F) = colim_{(W, x)} F(W)` is canonically `S(F)`, by
   `[W, x, t] ↦ [i, F(a) t]` for `x = [i, a]` and `[i, t] ↦ [U_i, [i, id], t]`.
6. The three clauses of Tag 00Y5 hold, so `u` is a point (Tag 00YC).
7. `R(E)(W) = Map(u(W), E)` is a sheaf: lifts over a covering are glued using lifts of
   pairs to the fibre products `W_k ×_W W_l`; empty coverings give one function.
8. Currying gives `T ⊣ R`, hence `S ⊣ R`; with step 3 this is a geometric morphism
   `Set → Sh(C)` with inverse image `S`, the construction of Tag 00YA(1).
-/
theorem inverseSystemSitePoint {C : Type u} [Category.{u} C]
    [HasFiniteLimits C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (U : Iᵒᵖ ⥤ C)
    (hcover : ∀ {K : Type u} {W : C} (V : K → C) (a : ∀ k, V k ⟶ W),
      Presieve.ofArrows V a ∈ J W →
      ∀ f : (inverseSystemHomFunctor U).obj W,
        ∃ (k : K) (g : (inverseSystemHomFunctor U).obj (V k)),
          (inverseSystemHomFunctor U).map (a k) g = f) :
    PreservesFiniteLimits (inverseSystemHomFunctor U) ∧
      (∀ (K : Type u) (W : C) (V : K → C) (a : ∀ k, V k ⟶ W)
        (_ : Presieve.ofArrows V a ∈ J W)
        (f : (inverseSystemHomFunctor U).obj W),
        ∃ (k : K) (g : (inverseSystemHomFunctor U).obj (V k)),
          (inverseSystemHomFunctor U).map (a k) g = f) ∧
      ∃ (p : GeometricMorphism (Type (max u w))
          (Sheaf J.toGrothendieck (Type (max u w)))),
        Nonempty (p.inverse ≅ inverseSystemSectionColimitFunctor.{w} J.toGrothendieck U) := by
  sorry

end CategoryTheory
