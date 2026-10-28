/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage

/-!
# Bounded constructible complexes are stable under `⊗ᴸ` once single sheaves are

Let `Λ` be a condensed ring and `X` a scheme such that the bounded constructible complexes of
`Λ_X`-modules form a triangulated subcategory of `D(Mod_{Λ_X})`. The unit `Λ_X` is bounded
constructible (`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_unit`). If
`F ⊗ᴸ G` is bounded constructible for any two constructible sheaves `F`, `G` placed in degree
`0`, then `K ⊗ᴸ L` is bounded constructible for any two bounded constructible complexes `K`, `L`
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_closure`, the dévissage
step of blueprint `lem-sfb-dc-tensor-preserves`): dévissage along the truncations
(`AlgebraicGeometry.ProEtale.boundedConstructible_obj_of_forall_singleFunctor`), first in `L`
(`K ⊗ᴸ -` is triangulated), then in `K` (`- ⊗ᴸ G` is triangulated).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})

/-- The coefficient ring `Λ_X`, placed in degree `0`, is the tensor unit of `D(Mod_{Λ_X})`,
and it is bounded constructible: its only cohomology sheaf is `Λ_X` itself in degree `0`,
which is constructible for the trivial stratification (it is free of rank `1`). This is the
unit clause of blueprint `lem-sfb-dc-tensor-preserves`. -/
theorem boundedConstructible_tensor_unit :
    boundedConstructible (condensedRingObj Λ X)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))) := by
  let R := condensedRingObj Λ X
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  let U := 𝟙_ (DerivedCategory C)
  let eUnit : (DerivedCategory.singleFunctor C 0).obj (𝟙_ C) ≅ U :=
    DerivedCategory.singleFunctorObjUnitIso C
  -- a zero module object is constructible: it is a cohomology sheaf of a zero complex
  have hzero (M : C) (hM : IsZero M) : IsConstructibleModuleObject R M := by
    obtain ⟨Z, hZ, hPZ⟩ := ObjectProperty.ContainsZero.exists_zero (P := boundedConstructible R)
    exact (hPZ.2 0).of_iso (((DerivedCategory.homologyFunctor C 0).map_isZero hZ).iso hM)
  have : U.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eUnit 0
  have : U.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eUnit 0
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact hzero _ (DerivedCategory.isZero_of_isGE U 0 n hn)
  · let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (𝟙_ C)
    have hr : IsConstructibleModuleObject R (Mod.regular R) := by
      refine ⟨Scheme.Stratification.trivial X, fun i ↦ ?_⟩
      refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
      let G := ProEtale.upperStar Ab.{u + 1} ((Scheme.Stratification.trivial X).immersion i)
      let H := ProEtale.upperStar Ab.{u + 1} (𝟙 ((Scheme.Stratification.trivial X).domain i))
      let e' : (H.mapMod (G.obj R)).obj ((G.mapMod R).obj (Mod.regular R)) ≅
          Mod.regular (H.obj (G.obj R)) :=
        Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
          MonoidalCategory.whiskerLeft_id, Category.id_comp])
      let e1 : Mod.regular (H.obj (G.obj R)) ≅ Mod.finiteFree (H.obj (G.obj R)) 1 :=
        (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (H.obj (G.obj R)))).symm
      exact ⟨1, 0, 0, ⟨e' ≪≫ e1 ≪≫
        (cokernelZeroIsoTarget (X := Mod.finiteFree (H.obj (G.obj R)) 0)
          (Y := Mod.finiteFree (H.obj (G.obj R)) 1)).symm⟩⟩
    exact hr.of_iso (e.symm ≪≫ (DerivedCategory.homologyFunctor C 0).mapIso eUnit)
  · exact hzero _ (DerivedCategory.isZero_of_isLE U 0 n hn)

/-- Dévissage step of blueprint `lem-sfb-dc-tensor-preserves`: if the bounded constructible
complexes of `Λ_X`-modules form a triangulated subcategory and `F ⊗ᴸ G` is bounded
constructible for any two constructible sheaves `F`, `G` placed in degree `0`, then the
bounded constructible complexes form a monoidal subcategory of `D(Mod_{Λ_X})` for the derived
tensor product (Bhatt–Scholze, Section 6.8; SGA 4½ [Th. finitude], 1.6).

Dévissage along the truncations
(`AlgebraicGeometry.ProEtale.boundedConstructible_obj_of_forall_singleFunctor`): first in the
second variable, `K ⊗ᴸ -` being triangulated, then in the first variable, `- ⊗ᴸ G` being
triangulated. -/
theorem boundedConstructible_tensor_closure
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated]
    (hsingle : ∀ (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)),
      IsConstructibleModuleObject (condensedRingObj Λ X) F →
      IsConstructibleModuleObject (condensedRingObj Λ X) G →
      boundedConstructible (condensedRingObj Λ X)
        (((-⊗ᴸ-(X)⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj F)).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))) :
    (boundedConstructible (condensedRingObj Λ X)).IsMonoidal where
  prop_unit := boundedConstructible_tensor_unit Λ X
  prop_tensor K _ hK hL :=
    boundedConstructible_obj_of_forall_singleFunctor (tensorLeft K)
      (fun G hG ↦ boundedConstructible_obj_of_forall_singleFunctor
        (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G))
        (fun F hF ↦ hsingle F G hF hG) hK) hL

end AlgebraicGeometry.ProEtale.CondensedRing
