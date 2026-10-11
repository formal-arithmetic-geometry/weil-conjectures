/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

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

## Sorried data

`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar` is, *temporarily*, a sorried
`Functor.Monoidal` structure, i.e. sorried data rather than a Prop about a constructed map.
The intended construction is the following.

1. The underived pullback `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` is strong monoidal for the
   relative tensor products: `mapMod(f^*) : Mod_{Λ_Y} ⥤ Mod_{f^* Λ_Y}` is, since `f^*` is
   strong monoidal and preserves the coequalizers defining `⊗_{Λ_Y}`, and so is the extension
   of scalars `Ext_{α_f}` (an isomorphism, `α_f` being one).
2. A strong monoidal functor `F` between abelian monoidal categories which preserves K-flat
   complexes and quasi-isomorphisms between them has a left derived functor `LF` which is
   oplax monoidal: `⊗ᴸ ∘ (LF × LF)` is a binary left derived functor of `Q ∘ ⊗ ∘ (F × F)`, and
   the oplax comparison `LF (A ⊗ᴸ B) ⟶ LF A ⊗ᴸ LF B` is obtained from its universal property
   applied to `LF (QA ⊗ᴸ QB) ⟶ LF (Q (A ⊗ B)) ≅ Q (F A ⊗ F B)`. It is an isomorphism, as is
   seen on K-flat resolutions.

Both steps are to be carried out on a separate branch; the instance below is the statement of
their outcome. Note that the canonical comparison maps are not recorded here: any use of this
structure is relative to it.

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

/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over `Λ` is
strong monoidal for the derived tensor products. See the module docstring: this is temporarily
sorried *data*. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦Λ⟧).Monoidal :=
  sorry

/-- The derived pullback of the tensor unit `Λ_Y` is the tensor unit `Λ_X`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦Λ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso L((f)^*⟦Λ⟧)).symm

/-- The derived pullback commutes with the derived tensor product:
`Lf^* (A ⊗ᴸ B) ≅ Lf^* A ⊗ᴸ Lf^* B`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).obj (A ⊗ B) ≅ L((f)^*⟦Λ⟧).obj A ⊗ L((f)^*⟦Λ⟧).obj B :=
  (Functor.Monoidal.μIso L((f)^*⟦Λ⟧) A B).symm

end AlgebraicGeometry.ProEtale.CondensedRing
