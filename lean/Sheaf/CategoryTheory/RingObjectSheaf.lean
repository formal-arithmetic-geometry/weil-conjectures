/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Monoidal.Mon

import Sheaf.CategoryTheory.SheafificationTensorLocalIso

/-!
# Ring objects associated to sheaves of rings

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-ring-object/det-def-sfb-ring-object-sheaf.md
  (blueprint: det-def-sfb-ring-object-sheaf); Stacks Tags 00YR and 00WH.

The helper `hasSheafCompose_forget₂_ringCat_ab` supplies the underlying-sheaf clause
without a universe restriction. `ringObjectOfSheafOfRings` states the transported
structure, its unique extensions and its compatibility with morphisms.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/-- Forgetting ring operations preserves sheaves on every site, independently of the
site and coefficient universes. Source: Stacks Tag 00YR, assertion (alpha), and
`det-def-sfb-ring-object-sheaf`, first conclusion
(blueprint: det-def-sfb-ring-object-sheaf).

Proof: the ring presheaf and its underlying abelian presheaf have the same
section sets and restrictions. Hence a matching family for one is a matching
family for the other, and the unique glued ring section gives its unique
abelian glued section. Addition, zero and negation commute with this gluing
by uniqueness. Thus the underlying abelian presheaf of every ring sheaf is a
sheaf, which is precisely `HasSheafCompose.isSheaf`. -/
@[instance]
theorem hasSheafCompose_forget₂_ringCat_ab
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w}) := by
  sorry

/-- In the situation of `det-def-sfb-ring-object-presheaf`, a sheaf of rings has a
canonical ring-object structure on its underlying abelian sheaf.  The counit of
sheafification is a ring-object isomorphism for the unique transported structure; its maps are
exactly the extensions of sectionwise multiplication and the integer unit, and
commutative sections and morphisms give commutative ring objects and monoid
morphisms. Source: Stacks Tags 00YR and 00WH and the blueprint node
`det-def-sfb-ring-object-sheaf`. (blueprint: det-def-sfb-ring-object-sheaf)

Proof, following the seven DAG steps:

1. Forgetting operations preserves matching families and their unique glued
sections; addition, zero and negatives respect gluing by uniqueness. This is
Stacks Tag 00YR and `hasSheafCompose_forget₂_ringCat_ab`.
2. By `def-weil-pbc-sheafification`, the identity of the underlying presheaf
extends uniquely to the counit `e`. The sheafification unit is the underlying
map of its inverse `q`: the two inverse identities follow by uniqueness of
extension. The same argument gives naturality of the unit.
3. Apply `det-def-sfb-ring-object-presheaf` to obtain a monoid object `A` on
the sheafification, with multiplication `a(μp)` after the monoidal comparison
and unit `a(ηp)`, preserving commutativity and ring morphisms.
4. Set `μ = (q ⊗ q) ≫ μA ≫ e` and `η = ηA ≫ e`, as in `MonObj.ofIso`.
In the associativity composites cancel `q ≫ e` and use tensor functoriality
and naturality of the associator to reduce to associativity on `A`.
Naturality of each unitor similarly reduces the unit axioms to those on `A`.
The two monoid-morphism equations hold for `e` and `q`; conversely they force
these displayed structure maps by cancellation. Thus the structure is unique
in the sense of `det-def-sfb-ring-object-monoid`.
5. `det-def-sfb-sheaf-tensor-structure` and clause 3 of
`det-def-sfb-sheaf-tensor-local-iso` identify the localized tensor with the
sheafification of the presheaf tensor. Its comparison with the underlying
presheaf tensor is `Functor.LaxMonoidal.μ` for `sheafToPresheaf`, the adjunct
of the inverse sheafification tensorator followed by the counits. Composing
with the displayed multiplication cancels the tensorator and inverse counits;
naturality and the triangle identity leave exactly `μp`. The analogous unit
comparison `Functor.LaxMonoidal.ε` leaves exactly `ηp`, namely `n ↦ n • 1`.
The sheafification universal property makes each such extension unique.
6. Sectionwise commutativity gives commutativity on `A` by step 3.
Naturality of the braiding transports this identity through `e` to the
quantified structure `m`, giving `IsCommMonObj` without assuming it initially.
7. For a ring-sheaf morphism `f`, the composites with source multiplication
and target multiplication have the same restriction, since the presheaf ring
map preserves products. Naturality of the tensor comparison and uniqueness
in step 5 give equality of the sheaf maps. The analogous argument for the
integer unit gives the other `IsMonHom` equation. Equivalently, naturality of
the counit writes `f` as the conjugate of its monoidal sheafification. -/
theorem ringObjectOfSheafOfRings
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal]
    (S : Sheaf J RingCat.{w}) :
    Presheaf.IsSheaf J (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) ∧
    IsIso ((sheafificationAdjunction J Ab.{w}).counit.app
      ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)) ∧
    (∃! (m : @MonObj (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
        ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)),
      m.one =
          @MonObj.one (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
            (Sheaf.sheafifyRingPresheaf J S.obj)
            (Sheaf.monObj_presheafToSheaf_obj J
              (S.obj ⋙ forget₂ RingCat.{w} Ab.{w})) ≫
              (Sheaf.sheafifyRingPresheafIso J S).hom ∧
      m.mul =
          (Sheaf.monoidalCategory J Ab.{w}).tensorHom
              (Sheaf.sheafifyRingPresheafIso J S).inv
              (Sheaf.sheafifyRingPresheafIso J S).inv ≫
            @MonObj.mul (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
              (Sheaf.sheafifyRingPresheaf J S.obj)
              (Sheaf.monObj_presheafToSheaf_obj J
                (S.obj ⋙ forget₂ RingCat.{w} Ab.{w})) ≫
            (Sheaf.sheafifyRingPresheafIso J S).hom ∧
      (@Functor.LaxMonoidal.μ (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
          (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
          (sheafToPresheafLaxMonoidal Ab.{w} J)
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ≫ m.mul.hom =
          @MonObj.mul (Cᵒᵖ ⥤ Ab.{w}) _ _
            (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂)) ∧
      (∀ g : (Sheaf.monoidalCategory J Ab.{w}).tensorObj
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ⟶
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S),
        @Functor.LaxMonoidal.μ (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
          (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
          (sheafToPresheafLaxMonoidal Ab.{w} J)
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ≫ g.hom =
          @MonObj.mul (Cᵒᵖ ⥤ Ab.{w}) _ _
            (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂) → g = m.mul) ∧
      (@Functor.LaxMonoidal.ε (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
          (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
          (sheafToPresheafLaxMonoidal Ab.{w} J) ≫ m.one.hom =
          @MonObj.one (Cᵒᵖ ⥤ Ab.{w}) _ _
            (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂)) ∧
      (∀ g : (Sheaf.monoidalCategory J Ab.{w}).tensorUnit ⟶
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S),
        @Functor.LaxMonoidal.ε (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
          (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
          (sheafToPresheafLaxMonoidal Ab.{w} J) ≫ g.hom =
          @MonObj.one (Cᵒᵖ ⥤ Ab.{w}) _ _
            (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂) → g = m.one) ∧
      ((∀ (U : Cᵒᵖ) (a b : S.obj.obj U), a * b = b * a) →
        @IsCommMonObj (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
          (Sheaf.braidedCategory J Ab.{w})
          ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) m)) ∧
    (∀ {T : Sheaf J RingCat.{w}} (f : S ⟶ T),
      @IsMonHom (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
        ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
        ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj T)
        (Sheaf.monObj_sheafCompose_obj J S) (Sheaf.monObj_sheafCompose_obj J T)
        ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f)) := by
  sorry

end CategoryTheory
