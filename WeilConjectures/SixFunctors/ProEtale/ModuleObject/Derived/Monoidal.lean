/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarTensor

/-!

# The monoidal structure of the derived pullback on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧) : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is strong monoidal for
the derived tensor products `- ⊗ᴸ_{Λ} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`:
```
Lf^* (A ⊗ᴸ_{Λ_Y} B) ≅ Lf^* A ⊗ᴸ_{Λ_X} Lf^* B,    Lf^* Λ_Y ≅ Λ_X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

## Construction

- The tensorator is the inverse of the comparison
  `ProEtale.CondensedRing.leftDerivedUpperStarTensorIso` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarTensor`.
- The unit comparison `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso` is
  `Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙) ≅ Qh 𝟙`: the counit of `Lf^*`, an isomorphism since `f^*` is
  exact, followed by the unit comparison of the strong monoidal underived pullback
  `ProEtale.CondensedRing.monoidal_upperStar` in degree `0`.

## Sorried input

The data is constructed; the associativity and the unitality of the structure are `sorry`ed.
They are checked on pairs (resp. triples) of K-flat complexes, where all the comparisons are
induced by the coherent tensorator of the underived pullback `f^*`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback of the tensor unit `Λ_Y` is the tensor unit `Λ_X`: the counit
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙)` of the derived pullback of the exact functor `f^*`, followed by the
unit comparison `f^* 𝟙 ≅ 𝟙` of the strong monoidal pullback of module objects, in degree `0`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦Λ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (f)^*⟦Λ⟧
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso (f)^*⟦Λ⟧).symm))

/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over `Λ` is
strong monoidal for the derived tensor products, with tensorator the inverse of
`leftDerivedUpperStarTensorIso` and unit comparison `leftDerivedUpperStarUnitIso`. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦Λ⟧).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (leftDerivedUpperStarUnitIso Λ f).symm
      μIso K L := (((leftDerivedUpperStarTensorIso Λ f).app K).app L).symm
      μIso_hom_natural_left φ L :=
        NatTrans.congr_app ((leftDerivedUpperStarTensorIso Λ f).inv.naturality φ) L
      μIso_hom_natural_right K ψ :=
        ((leftDerivedUpperStarTensorIso Λ f).inv.app K).naturality ψ
      associativity := sorry
      left_unitality := sorry
      right_unitality := sorry }

end AlgebraicGeometry.ProEtale.CondensedRing
