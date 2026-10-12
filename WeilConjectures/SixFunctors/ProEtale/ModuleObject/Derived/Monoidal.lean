/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# The monoidal structure of the derived pullback on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧) : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is strong monoidal
for the derived tensor products `- ⊗ᴸ_Λ -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`:
```
Lf^* (A ⊗ᴸ_{Λ_Y} B) ≅ Lf^* A ⊗ᴸ_{Λ_X} Lf^* B,    Lf^* Λ_Y ≅ Λ_X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

The file also records the monoidal closed structure of the bounded constructible derived
categories `Dᵇc(X)⟦Λ⟧`: they are full monoidal closed subcategories of `D(Mod_{Λ_X})` as soon as
they contain the unit and are stable under `⊗ᴸ` and `RHom`
(`ObjectProperty.IsMonoidal`, `ObjectProperty.IsMonoidalClosed`), and the restriction
`boundedConstructibleUpperStar` of `Lf^*` is then oplax monoidal
(`ProEtale.CondensedRing.oplaxMonoidal_boundedConstructibleUpperStar`).

## Sorried data

`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar` is, *temporarily*, a sorried
`Functor.Monoidal` structure, i.e. sorried data rather than a Prop about a constructed map.
The intended construction is the following.

1. The underived pullback `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` is strong monoidal for the
   relative tensor products: `mapMod(f^*) : Mod_{Λ_Y} ⥤ Mod_{f^* Λ_Y}` is, since `f^*` is
   strong monoidal and preserves the coequalizers defining `⊗_{Λ_Y}`, and so is the extension
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

## Sorried input

- `ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
  `ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`: for `X` separated of finite
  type over `k`, the bounded constructible complexes contain `Λ_X` and are stable under `⊗ᴸ` and
  `RHom`. Stability is `boundedConstructible_derivedTensor_obj` and
  `boundedConstructible_derivedHom_obj`; that `Λ_X` is constructible is not stated on master.
  They are lemmas rather than instances, the base field `k` not being determined by the
  conclusion: downstream statements take the two properties as instance arguments.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

/-! ### Oplax monoidal restrictions to full monoidal subcategories -/

namespace CategoryTheory.ObjectProperty

open MonoidalCategory Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  (F : C ⥤ D) [F.OplaxMonoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- The restriction `Q.lift (P.ι ⋙ F)` of an oplax monoidal functor `F` to full monoidal
subcategories is oplax monoidal, with the comparison maps of `F`. -/
noncomputable instance oplaxMonoidalLift : (Q.lift (P.ι ⋙ F) hF).OplaxMonoidal where
  η := ObjectProperty.homMk (η F)
  δ X Y := ObjectProperty.homMk (δ F X.obj Y.obj)
  δ_natural_left f X' := ObjectProperty.hom_ext _ (δ_natural_left F f.hom X'.obj)
  δ_natural_right X f := ObjectProperty.hom_ext _ (δ_natural_right F X.obj f.hom)
  oplax_associativity X Y Z :=
    ObjectProperty.hom_ext _ (oplax_associativity F X.obj Y.obj Z.obj)
  oplax_left_unitality X := ObjectProperty.hom_ext _ (oplax_left_unitality F X.obj)
  oplax_right_unitality X := ObjectProperty.hom_ext _ (oplax_right_unitality F X.obj)

end CategoryTheory.ObjectProperty

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The derived pullback is strong monoidal -/

section Ambient

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over
`Λ` is strong monoidal for the derived tensor products. See the module docstring: this is
temporarily sorried *data*. -/
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

end Ambient

/-! ### The monoidal closed structure on bounded constructible complexes -/

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BoundedConstructible

include ℓ k

variable (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]

/-- The bounded constructible complexes on `X` contain the unit `Λ_X` and are stable under the
derived tensor product, so `Dᵇc(X)⟦Λ⟧` is a full monoidal subcategory of `D(Mod_{Λ_X})`. -/
lemma isMonoidal_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X)).IsMonoidal :=
  sorry

/-- The bounded constructible complexes on `X` are stable under the derived hom, so
`Dᵇc(X)⟦Λ⟧` is a full monoidal closed subcategory of `D(Mod_{Λ_X})`. -/
lemma isMonoidalClosed_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X)).IsMonoidalClosed :=
  sorry

end BoundedConstructible

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [(boundedConstructible (condensedRingObj Λ X)).IsMonoidal]
  [(boundedConstructible (condensedRingObj Λ Y)).IsMonoidal]

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes is
oplax monoidal, with the comparison maps of `L((f)^*⟦Λ⟧)`. -/
noncomputable instance oplaxMonoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar Λ ℓ k f).OplaxMonoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.oplaxMonoidalLift _ _

end UpperStar

end AlgebraicGeometry.ProEtale.CondensedRing
