/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Finite limits of internal abelian groups

Source: Stacks Project, Sites and Sheaves, Tag 00YV, abelian-group part and preceding
quadruple discussion (blueprint: lem-sfb-internal-abelian-finite-limit-creation).
The finite-limit-category formulation is the categorical argument extracted from that passage.
-/

@[expose] public section

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.CommGrp

/-- Source: Stacks Project, Tag 00YV, abelian-group part and preceding quadruple discussion
(blueprint: lem-sfb-internal-abelian-finite-limit-creation).

The Cartesian monoidal structures specify chosen terminal objects and binary products; they
exist in every category with finite limits. The braidings are uniquely determined by these
products. Multiplication, one and inverse in `CommGrp` mean addition, zero and negation.
The subtype in the first clause fixes the underlying object literally, rather than up to
isomorphism. The equalities of forgetful functors in the last clause specify the underlying
object and morphism maps literally; `eqToIso` only supplies the corresponding type casts.

Proof (using def-galois-finite-limits-colimits and def-weil-category-product):
(1) The projections of any underlying limit are jointly monic, by uniqueness of
factorizations, also for the empty diagram. (2) Multiplication, unit and inverse in the diagram
form cones with vertices the square of the limit, the terminal object and the limit itself.
Their unique factorizations define its three operations. (3) Compose the two associativity
expressions with every projection and use the corresponding law in each diagram object;
joint monicity gives associativity. The same argument gives commutativity. (4) The two unit
and two inverse laws follow by the same projection test and terminal uniqueness. Any other
structure making the projections homomorphisms has the same three operations by limit
uniqueness. (5) For a cone of group objects, its unique underlying factorization preserves
each operation: compose the required equation with every projection. Faithfulness gives
uniqueness as a group morphism. (6) Conversely, compare a limiting group cone with the lifted
underlying limit. The two universal properties give mutually inverse cone maps, so its
underlying cone is limiting. These steps give creation, preservation and reflection.
(7) For the empty diagram all operations and laws are unique maps to a terminal object,
and every object has a unique homomorphism to it. (8) Product and terminal comparisons for
a finite-limit-preserving functor are invertible; projection tests give their compatibility
with pairings, product maps and terminal maps. (9) Induct on terms in multiplication, unit,
inverse and variables to show that transported terms agree with images of terms after the
product comparison. (10) Apply this to the two sides of every group law, obtaining the laws
for the transported operations. (11) Naturality of comparisons shows that images of
homomorphisms preserve all operations; functoriality gives the asserted functor.
(12) Forget a limiting group cone, apply preservation by the original functor, and reflect
its image limit using step (5) in the target category. This includes the empty limit. -/
theorem finiteLimitCreation
    (C : Type u) [Category.{v} C] [HasFiniteLimits C]
    [CartesianMonoidalCategory C] [BraidedCategory C] :
    (∀ (I : Type w) [SmallCategory I] [FinCategory I]
        (D : I ⥤ CommGrp C) (c : Cone (D ⋙ forget C)),
      IsLimit c →
        ∃! A : { A : CommGrp C // A.X = c.pt },
          (∀ j : I, ∃ f : A.val ⟶ D.obj j,
            eqToHom A.property.symm ≫ (forget C).map f = c.π.app j) ∧
          ∃ s : Cone D, s.pt = A.val ∧ (forget C).mapCone s = c ∧ Nonempty (IsLimit s)) ∧
    (∀ (I : Type w) [SmallCategory I] [FinCategory I]
        (D : I ⥤ CommGrp C) (c : Cone D),
      Nonempty (IsLimit c) ↔ Nonempty (IsLimit ((forget C).mapCone c))) ∧
    Nonempty (CreatesFiniteLimits (forget C)) ∧
    PreservesFiniteLimits (forget C) ∧ ReflectsFiniteLimits (forget C) ∧
    (∀ (E : Type u') [Category.{v'} E] [HasFiniteLimits E]
        [CartesianMonoidalCategory E] [BraidedCategory E]
        (F : C ⥤ E) [PreservesFiniteLimits F],
      ∃ (H : CommGrp C ⥤ CommGrp E) (hH : H ⋙ forget E = forget C ⋙ F),
        (∀ A : CommGrp C,
          MonObj.mul (X := (H.obj A).X) ≫ (eqToIso hH).hom.app A =
            ((eqToIso hH).hom.app A ⊗ₘ (eqToIso hH).hom.app A) ≫
              (prodComparisonIso F A.X A.X).inv ≫ F.map (MonObj.mul (X := A.X)) ∧
          MonObj.one (X := (H.obj A).X) ≫ (eqToIso hH).hom.app A =
            (preservesTerminalIso F).inv ≫ F.map (MonObj.one (X := A.X)) ∧
          GrpObj.inv (X := (H.obj A).X) ≫ (eqToIso hH).hom.app A =
            (eqToIso hH).hom.app A ≫ F.map (GrpObj.inv (X := A.X))) ∧
        PreservesFiniteLimits H) := by
  sorry

end CategoryTheory.CommGrp
