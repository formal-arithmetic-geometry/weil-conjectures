/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Underived free-source scalar comparison

Source: Stacks Project, Tags 03FD, 03D3 and 03D7.
(blueprint: lem-sbc-raw-module-free-source-hom-bijective).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The explicit generator comparison is bijective on underived Hom.
Source: Stacks Project, Tag 03FD, equality of section complexes; Tags 03D3 and 03D7.
(blueprint: lem-sbc-raw-module-free-source-hom-bijective).

Proof: Apply the inverse-image/direct-image adjunction in modules and in
abelian sheaves. Then apply sheafification adjunction, the free-module/free-group
adjunction and Yoneda. Both Hom groups become the same section group of f_*M
at U. The two units commute with the Kan-extension/sheafification comparison
pullbackIso. The definition of freeMap sends the identity generator to the
identity generator, so f ↦ a ≫ forget(f) becomes the identity on that section
group. It is therefore bijective. This works for every M, independently of
injectivity, in degree zero, over the zero ring, and on empty schemes. -/
theorem rawModuleFreeSourceHom_bijective
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun g :
        (upperStar (ModuleCat.{u + 1} Λ) f).obj ((freeSheaf Λ S).obj U) ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
          (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f ((freeSheaf Λ S).obj U)) ≫
          (RawModuleScalarComparison.forget Λ X).map g) := by sorry

end AlgebraicGeometry.Etale
