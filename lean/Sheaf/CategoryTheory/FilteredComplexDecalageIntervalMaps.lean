/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageTower

/-! # Changing the endpoints of a decalage interval

Source: Mathlib's natural mapping-cone comparison and Stacks Project, Tag 012K.
(blueprint: lem-sp-filtered-complex-decalage-interval-maps).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A square of tower intervals induces the corresponding square of cokernel sequences. -/
noncomputable def filteredComplexDecalageIntervalHom
    (U : FilteredObject (CochainComplex C ℤ))
    {a b a' b' : EInt} (h : a ≤ b) (h' : a' ≤ b')
    (α : ComposableArrows.mk₁ (homOfLE h) ⟶ ComposableArrows.mk₁ (homOfLE h')) :
    U.filtration.decalageTowerInterval a b h ⟶
      U.filtration.decalageTowerInterval a' b' h' where
  τ₁ := U.filtration.decalageTower.map (α.app 0)
  τ₂ := U.filtration.decalageTower.map (α.app 1)
  τ₃ := cokernel.map _ _
    (U.filtration.decalageTower.map (α.app 0))
    (U.filtration.decalageTower.map (α.app 1))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg U.filtration.decalageTower.map (Subsingleton.elim _ _))
  comm₁₂ := by
    change U.filtration.decalageTower.map (α.app 0) ≫
        U.filtration.decalageTower.map (homOfLE h') =
      U.filtration.decalageTower.map (homOfLE h) ≫ U.filtration.decalageTower.map (α.app 1)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg U.filtration.decalageTower.map (Subsingleton.elim _ _)
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The cone-to-quotient cohomology comparison commutes with endpoint squares.
Source: Mathlib `CochainComplex.mappingCone.descShortComplex_naturality`.
(blueprint: lem-sp-filtered-complex-decalage-interval-maps).

Proof. The square defines a morphism of the two cokernel short complexes.
Naturality of the mapping-cone-to-cokernel map gives a commuting square of
complexes. Apply homology, then use naturality of the homotopy-category homology
factorization and compose its comparison isomorphisms. -/
@[reassoc]
theorem filteredComplexDecalageIntervalIso_map
    (U : FilteredObject (CochainComplex C ℤ))
    {a b a' b' : EInt} (h : a ≤ b) (h' : a' ≤ b')
    (α : ComposableArrows.mk₁ (homOfLE h) ⟶ ComposableArrows.mk₁ (homOfLE h')) (n : ℤ) :
    (((filteredComplexDecalageSpectralObjectFunctor C).obj U).H n).map α ≫
        (filteredComplexDecalageIntervalIso U a' b' h' n).hom =
      (filteredComplexDecalageIntervalIso U a b h n).hom ≫
        HomologicalComplex.homologyMap (filteredComplexDecalageIntervalHom U h h' α).τ₃ n := by
  let T := filteredComplexDecalageIntervalHom U h h' α
  let f := CochainComplex.mappingCone.map
    (U.filtration.decalageTower.map (homOfLE h))
    (U.filtration.decalageTower.map (homOfLE h')) T.τ₁ T.τ₂ T.comm₁₂.symm
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) n
  let e := HomotopyCategory.homologyFunctorFactors C (.up ℤ) n
  have hmap : (((filteredComplexDecalageSpectralObjectFunctor C).obj U).H n).map α =
      (HomotopyCategory.homologyFunctor C (.up ℤ) n).map
        ((HomotopyCategory.quotient C (.up ℤ)).map f) := by
    rfl
  rw [hmap]
  change (HomotopyCategory.homologyFunctor C (.up ℤ) n).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
        (e.app _).hom ≫ H.map (U.filtration.decalageTowerConeToQuotient a' b' h') =
      ((e.app _).hom ≫ H.map (U.filtration.decalageTowerConeToQuotient a b h)) ≫ H.map T.τ₃
  rw [← Category.assoc]
  erw [e.hom.naturality f]
  rw [Category.assoc, ← H.map_comp]
  have hf : f ≫ U.filtration.decalageTowerConeToQuotient a' b' h' =
      U.filtration.decalageTowerConeToQuotient a b h ≫ T.τ₃ :=
    CochainComplex.mappingCone.descShortComplex_naturality T
  rw [hf, H.map_comp, Category.assoc]
  rfl

end CategoryTheory
