/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Derived section functors under an additive equivalence

Source: Stacks Project, Derived Categories, Tag 015M, lemma-compose-derived-functors,
with Tags 013K, 013P and 05TD for resolutions, their maps and degree zero
(blueprint: lem-exc-equivalence-derived-sections).
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open Category Limits

/-- The specified injective resolution transported termwise along an additive equivalence.
Its augmentation is the image of the given augmentation, using the canonical identification
of the image of a degree-zero single complex with the single complex of the image.
The equivalence preserves injectives, finite limits and colimits, hence quasi-isomorphisms.
Source: Stacks Project, Tag 015M, proof on the complex `F(I)`, and Tag 015Z
(blueprint: lem-exc-equivalence-derived-sections). -/
noncomputable def InjectiveResolution.equivalenceImage
    {C : Type u₁} {B : Type u₂} [Category.{v₁} C] [Category.{v₂} B]
    [Abelian C] [Abelian B] {X : C} (I : InjectiveResolution X)
    (E : C ⥤ B) [E.Additive] [E.IsEquivalence] : InjectiveResolution (E.obj X) where
  cocomplex := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := E.injective_obj_of_injective (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex E (ComplexShape.up ℕ) 0).inv.app X ≫
    (E.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

/-- An additive equivalence intertwining left exact section functors intertwines all their
right derived functors. The comparison is computed by the given natural isomorphism on
*every* injective resolution, and its degree-zero normalization is that same isomorphism.
Source: Stacks Project, Tag 015M, exact-equivalence special case; Tag 05TD for degree zero
(blueprint: lem-exc-equivalence-derived-sections).

Proof:
1. Enough injectives gives a resolution by successively embedding cokernels into injectives
   (def-sp-enough-injectives, def-sp-injective-resolutions, def-sp-abelian; Tag 013K).
2. The equivalence preserves injectives and exactness, so its termwise image is the resolution
   `I.equivalenceImage E` (lem-weil-pbc-equivalence-injective-resolutions; Tag 015Z).
3. Naturality of `α` on each differential makes its components an isomorphism of complexes;
   its termwise inverse is a chain map as well. Taking cohomology gives inverse maps.
4. Conjugate this cohomology map by `I.isoRightDerivedObj S q` and the corresponding
   isomorphism for `T` on the transported resolution (lem-weil-pbc-derived-functor-map-via-lift).
   This gives the stated component formula and invertibility.
5. Lift any object morphism to a map of resolutions (lem-weil-pbc-injective-resolution-lift-exists,
   Tag 013P). Apply the map formula of lem-weil-pbc-derived-functor-map-via-lift twice and
   naturality of `α` on the lift. Cancellation of the resolution isomorphisms gives naturality.
6. Apply the same square to the identity between any two resolutions. The derived maps are
   identities, proving resolution independence. Inverse components are natural by cancellation.
7. In degree zero, left exactness identifies each section object with the kernel of the first
   differential, via its augmentation (lem-weil-pbc-left-exact-injective-resolution-degree-zero).
   There are no negative-degree boundaries. Naturality of `α` on the augmentation gives the
   last equality under the canonical degree-zero identifications of lem-sp-derived-well-defined.
-/
theorem exists_equivalence_derivedSections
    {C : Type u₁} {B : Type u₂} {D : Type u₃}
    [Category.{v₁} C] [Category.{v₂} B] [Category.{v₃} D]
    [Abelian C] [Abelian B] [Abelian D] [EnoughInjectives C] [EnoughInjectives B]
    (E : C ⥤ B) [E.Additive] [E.IsEquivalence]
    (S : C ⥤ D) (T : B ⥤ D) [S.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteLimits T] (α : S ≅ E ⋙ T) :
    ∃ c : ∀ q : ℕ, S.rightDerived q ≅ E ⋙ T.rightDerived q,
      (∀ (q : ℕ) (X : C) (I : InjectiveResolution X),
        (c q).hom.app X ≫ ((I.equivalenceImage E).isoRightDerivedObj T q).hom =
          (I.isoRightDerivedObj S q).hom ≫
            HomologicalComplex.homologyMap
              ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex) q) ∧
      (c 0).hom ≫ Functor.whiskerLeft E T.rightDerivedZeroIsoSelf.hom =
        S.rightDerivedZeroIsoSelf.hom ≫ α.hom := by
  sorry

end CategoryTheory
