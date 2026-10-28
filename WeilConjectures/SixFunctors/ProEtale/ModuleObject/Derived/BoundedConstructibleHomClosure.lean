/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.InternalHomExact
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bounded constructible complexes are stable under `RHom` once single sheaves are

Let `Λ` be a condensed ring and `X` a scheme such that the bounded constructible complexes of
`Λ_X`-modules form a triangulated subcategory of `D(Mod_{Λ_X})`. If `RHom(F, G)` is bounded
constructible for any two constructible sheaves `F`, `G` placed in degree `0`, then
`RHom(K, L)` is bounded constructible for any two bounded constructible complexes `K`, `L`
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_hom_closure`, the dévissage step
of blueprint `lem-sfb-dc-hom-preserves`): dévissage along the truncations, first in `L`
(`RHom(K, -)` is triangulated, being a right adjoint of the triangulated functor `K ⊗ᴸ -`), then
in `K` (`RHom(-, G)` is triangulated, `DerivedCategory.internalHom_flip_obj_isTriangulated`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})

/-- Dévissage step of blueprint `lem-sfb-dc-hom-preserves`: if the bounded constructible
complexes of `Λ_X`-modules form a triangulated subcategory and `RHom(F, G)` is bounded
constructible for any two constructible sheaves `F`, `G` placed in degree `0`, then the bounded
constructible complexes are stable under `RHom(-, -)` (Bhatt–Scholze, Remark 6.8.15; Stacks,
Tag 08JC).

Dévissage along the truncations (`DerivedCategory.prop_of_bounded`): in the second variable
`RHom(K, -)` is triangulated, being right adjoint to the triangulated functor `K ⊗ᴸ -`; in the
first variable `RHom(-, G)` is triangulated by
`DerivedCategory.internalHom_flip_obj_isTriangulated`. -/
theorem boundedConstructible_hom_closure
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated]
    (hsingle : ∀ (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)),
      IsConstructibleModuleObject (condensedRingObj Λ X) F →
      IsConstructibleModuleObject (condensedRingObj Λ X) G →
      boundedConstructible (condensedRingObj Λ X)
        (((derivedHom Λ X).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj F))).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))) :
    (boundedConstructible (condensedRingObj Λ X)).IsMonoidalClosed := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let P := boundedConstructible (condensedRingObj Λ X)
  let Q : ObjectProperty C := fun F ↦ IsConstructibleModuleObject (condensedRingObj Λ X) F
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ IsConstructibleModuleObject.of_iso e h⟩
  have : IsGrothendieckAbelian.{u + 1} C :=
    Mod.isGrothendieckAbelian.{u + 1, u + 1, u + 2} _
  have : Abelian.HasFunctorialFlatResolution C :=
    Mod.hasFunctorialFlatResolution.{u + 1, u + 2}
      (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X)
  refine ⟨fun K L hK hL ↦ ?_⟩
  let H := (derivedHom Λ X).obj (op K)
  let : ((derivedTensor Λ X).obj K).CommShift ℤ := DerivedCategory.commShiftTensorLeft C K
  have : ((derivedTensor Λ X).obj K).IsTriangulated := DerivedCategory.isTriangulated_tensorLeft C K
  let adj := derivedTensorHomAdjunction Λ K
  let : H.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : H.IsTriangulated := adj.isTriangulated_rightAdjoint
  refine DerivedCategory.prop_of_bounded (P.inverseImage H) Q (fun G hG ↦ ?_) L hL.1 hL.2
  let W := (DerivedCategory.singleFunctor C 0).obj G
  let F := (derivedHom Λ X).flip.obj W
  obtain ⟨s, hs⟩ := DerivedCategory.internalHom_flip_obj_isTriangulated.{u + 2, u + 1} C W
  let : F.CommShift ℤ := s
  have : F.IsTriangulated := hs
  exact DerivedCategory.prop_of_bounded (P.inverseImage F).unop Q
    (fun F hF ↦ hsingle F G hF hG) K hK.1 hK.2

end AlgebraicGeometry.ProEtale.CondensedRing
