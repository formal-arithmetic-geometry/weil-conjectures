/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.CategoryTheory.UniverseCondensedActionModule
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Ordinary discrete actions and internal condensed actions

Source: latest blueprint, direct-image stability proof, paragraph (3); agent-formulated
algebraic input by finite clopen fiber gluing, with external reference WANTED
(blueprint: lem-sfb-discrete-condensed-action-equivalence).

The strict equalities of underlying functors retain objects and morphisms. The fiber
formula is stated after every profinite map into a fiber; in particular it gives the
formula on its clopen profinite inclusion. The equality transports are identity maps
on the specified underlying modules, rather than arbitrary comparison isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace Profinite.CondensedAction.Universe

/-- Ordinary actions extend uniquely to natural sectionwise actions of continuous maps
into the discrete group, additively and over the original internal-module category.
Source: latest blueprint, direct-image stability proof, paragraph (3), algebraic input
(blueprint: lem-sfb-discrete-condensed-action-equivalence).

Proof:
1. Apply the internal/sectionwise module equivalence and the coherent sheaf criterion.
Restriction to a finite disjoint clopen partition is a bijective linear map to the product
of the section modules. This includes the empty partition, giving zero sections on empty.
2. A continuous map from a compact space into a discrete group has finite range. Its
fibers are clopen profinite subspaces and their inclusions are a finite covering family.
3. Glue the sections obtained by applying the ordinary automorphism on each fiber.
Restriction detects equality, so the resulting section action is linear.
4. Check the identity on fibers and multiplication on the common refinement of the two
fiber partitions. This gives the group action in the left-action order.
5. Pull back the fiber partition along any profinite map. Naturality of the ordinary
module automorphisms and uniqueness of gluing give section-action naturality.
6. Retain each equivariant map: it commutes with the glued actions after restriction to
each fiber. Identity, composition, zero and addition are unchanged, giving additivity.
7. Conversely, evaluate a section action at each constant group-valued function. Its
naturality and linearity give an internal module automorphism through the recorded
internal/sectionwise module equivalence; the group law gives the ordinary action.
8. Extending and then restricting returns the ordinary action, including at empty tests.
Restricting and extending returns the section action by naturality along each fiber and
uniqueness of gluing. Both composites retain maps; identity maps give unit and counit.
9. Trivial actions extend to trivial actions and restrict to trivial actions. The trivial
group, empty test, zero module and zero ring require no exclusion: empty partitions and
zero section modules make all the same formulas valid.
-/
theorem exists_discreteActionEquivalence
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (G : Type (u + 1)) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    ∃ (E : (SingleObj G ⥤ Modules R) ≌ ActionModule R G)
      (hforward : E.functor ⋙ forgetAction =
        (evaluation (SingleObj G) (Modules R)).obj (SingleObj.star G))
      (hinverse : E.inverse ⋙ (evaluation (SingleObj G) (Modules R)).obj
        (SingleObj.star G) = forgetAction),
      E.functor.Additive ∧ E.inverse.Additive ∧
      Functor.const (SingleObj G) ⋙ E.functor = trivial ∧
      trivial ⋙ E.inverse = Functor.const (SingleObj G) ∧
      (∀ (S : Profinite.{u}) (g : C(S, G)),
        (Set.range g).Finite ∧ ∀ a : G, IsClopen (g ⁻¹' {a})) ∧
      (∀ (F : SingleObj G ⥤ Modules R) (S T : Profinite.{u}) (f : T ⟶ S)
        (g : C(S, G)) (a : G), a ∈ Set.range g → (∀ t : T, g (f t) = a) →
        ∀ m : sectionModule R (E.functor.obj F).module S,
        ((eqToHom (Functor.congr_obj hforward F)).hom.hom.app (op T)).hom
          (((E.functor.obj F).module.X.obj.map f.op).hom
            ((E.functor.obj F).act S g m)) =
        ((F.map a).hom.hom.app (op T)).hom
          (((F.obj (SingleObj.star G)).X.obj.map f.op).hom
            (((eqToHom (Functor.congr_obj hforward F)).hom.hom.app (op S)).hom
              m))) ∧
      (∀ (M : ActionModule R G) (S : Profinite.{u}) (a : G)
        (m : sectionModule R ((E.inverse.obj M).obj (SingleObj.star G)) S),
        ((eqToHom (Functor.congr_obj hinverse M)).hom.hom.app (op S)).hom
          ((((E.inverse.obj M).map a).hom.hom.app (op S)).hom m) =
        M.act S (ContinuousMap.const S a)
          (((eqToHom (Functor.congr_obj hinverse M)).hom.hom.app (op S)).hom m)) := by
  sorry

end Profinite.CondensedAction.Universe
