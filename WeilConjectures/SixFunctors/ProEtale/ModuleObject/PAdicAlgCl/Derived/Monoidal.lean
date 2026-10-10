/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.UpperLowerStar

/-!

# The monoidal structure of the derived pullback on module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime and `f : X ⟶ Y` a morphism of schemes. The derived pullback
`Lf^* = L((f)^*⟦ℚ̄_ℓ⟧) : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.UpperLowerStar` is
strong monoidal for the derived tensor products `- ⊗ᴸ_{ℚ̄_ℓ} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Tensor`:
```
Lf^* (A ⊗ᴸ_{ℚ̄_ℓ,Y} B) ≅ Lf^* A ⊗ᴸ_{ℚ̄_ℓ,X} Lf^* B,    Lf^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

## Sorried data

`ProEtale.PadicAlgClRing.monoidal_leftDerivedUpperStar` is, *temporarily*, a sorried
`Functor.Monoidal` structure, i.e. sorried data rather than a Prop about a constructed map.
The intended construction is the following.

1. The underived pullback `(f)^*⟦ℚ̄_ℓ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` is strong monoidal for the
   relative tensor products: `mapMod(f^*) : Mod_{ℚ̄_ℓ,Y} ⥤ Mod_{f^* ℚ̄_ℓ,Y}` is, since `f^*` is
   strong monoidal and preserves the coequalizers defining `⊗_{ℚ̄_ℓ,Y}`, and so is the extension
   of scalars `Ext_{α_f}`.
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

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback `Lf^* : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` on module objects over
`ℚ̄_ℓ` is strong monoidal for the derived tensor products. See the module docstring: this is
temporarily sorried *data*. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦ℚ̄_ℓ⟧).Monoidal :=
  sorry

/-- The derived pullback of the tensor unit `ℚ̄_ℓ,Y` is the tensor unit `ℚ̄_ℓ,X`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦ℚ̄_ℓ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso L((f)^*⟦ℚ̄_ℓ⟧)).symm

/-- The derived pullback commutes with the derived tensor product:
`Lf^* (A ⊗ᴸ B) ≅ Lf^* A ⊗ᴸ Lf^* B`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    L((f)^*⟦ℚ̄_ℓ⟧).obj (A ⊗ B) ≅ L((f)^*⟦ℚ̄_ℓ⟧).obj A ⊗ L((f)^*⟦ℚ̄_ℓ⟧).obj B :=
  (Functor.Monoidal.μIso L((f)^*⟦ℚ̄_ℓ⟧) A B).symm

end AlgebraicGeometry.ProEtale.PadicAlgClRing
