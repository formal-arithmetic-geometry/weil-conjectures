/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# The six functors on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, Λ_X)` of module objects over the coefficient ring object
`Λ_X = p_X^* Λ` is the full subcategory
`ProEtale.BoundedConstructible (condensedRingObj Λ X)` of `D(Mod_{Λ_X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦Λ⟧`. This file restricts the six functors on `D(Mod_{Λ_X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived` to these full
subcategories:

| functor | restriction | hypotheses |
| --- | --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` | `X`, `Y` noetherian |
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` | and `f` of finite type |
| `Rf_! = R(f)_!⟦Λ⟧` | `boundedConstructibleLowerShriek` | and `HasCompactification f` |
| `j_! = D((j)_!open⟦Λ⟧)` | `boundedConstructibleOpenImmersionLowerShriek` | `j` an open immersion |
| `Rf^! = R(f)^!⟦Λ⟧` | `boundedConstructibleUpperShriek` | and `HasCompactification f` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` | `X` noetherian |
| `RHom(-, -)` | `boundedConstructibleHom` | `X` noetherian |

Each restriction is the `ObjectProperty.lift` of the composite of the inclusion with the functor
on the ambient derived category, so it is compatible with the inclusions by construction
(`ObjectProperty.liftCompιIso`). The adjunctions `Lf^* ⊣ Rf_*`, `j_! ⊣ j^*`, `Rf_! ⊣ Rf^!` and
`K ⊗ᴸ - ⊣ RHom(K, -)` restrict along the fully faithful inclusions
(`Adjunction.restrictFullyFaithful`), and so does the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`).

Here "noetherian" means that the underlying topological space is noetherian, which is also the
hypothesis under which `ProEtale.boundedConstructible` is triangulated.

## Sorried input

That the six functors preserve bounded constructible complexes is `sorry`ed:
`boundedConstructible_leftDerivedUpperStar_obj`, `boundedConstructible_rightDerivedLowerStar_obj`,
`boundedConstructible_openImmersionLowerShriek_obj`,
`boundedConstructible_rightDerivedLowerShriek_obj`,
`boundedConstructible_rightDerivedUpperShriek_obj`, `boundedConstructible_derivedTensor_obj` and
`boundedConstructible_derivedHom_obj`.

Warning: the hypotheses are deliberately minimal and are not the ones under which these
statements are theorems. For `Rf_*`, `Rf^!` and `RHom` one needs Deligne's finiteness theorem,
i.e. schemes of finite type over a regular base of dimension `≤ 1` on which `ℓ` is invertible,
and for all six functors the coefficient ring `Λ` should be `𝒪_E` or `E` for a finite extension
`E` of `ℚ_ℓ`. The hypotheses are to be strengthened when the statements are proved.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits Opposite TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [NoetherianSpace X] [NoetherianSpace Y]

/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : boundedConstructible (condensedRingObj Λ Y) K) :
    boundedConstructible (condensedRingObj Λ X) ((L((f)^*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Scheme.{u}} [NoetherianSpace Z]
    (g : Y ⟶ Z) :
    boundedConstructibleUpperStar Λ (f ≫ g) ≅
      boundedConstructibleUpperStar Λ g ⋙ boundedConstructibleUpperStar Λ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ f).symm ≪≫
      (Functor.associator _ _ _).symm)

variable [LocallyOfFiniteType f] [QuasiCompact f]

/-- The derived pushforward `Rf_*` on module objects over `Λ` along a morphism of finite
type preserves bounded constructible complexes. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ Y) ((R((f)_*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleLowerStar : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f)_*⟦Λ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar Λ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar Λ f ⊣ boundedConstructibleLowerStar Λ f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ f).symm
    (boundedConstructibleLowerStarCompatibility Λ f).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [NoetherianSpace U]
  [NoetherianSpace X]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (hK : boundedConstructible (condensedRingObj Λ U) K) :
    boundedConstructible (condensedRingObj Λ X) ((D((j)_!open⟦Λ⟧)).obj K) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ j ⊣ boundedConstructibleUpperStar Λ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ j).symm
    (boundedConstructibleUpperStarCompatibility Λ j).symm

end OpenImmersion

/-! ### The exceptional functors -/

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [NoetherianSpace X] [NoetherianSpace Y]

/-- The derived lower shriek `Rf_!` on module objects over `Λ` preserves bounded
constructible complexes. -/
lemma boundedConstructible_rightDerivedLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ Y) ((R(f)_!⟦Λ⟧).obj K) :=
  sorry

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R(f)_!⟦Λ⟧`. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R(f)_!⟦Λ⟧)
    fun K ↦ boundedConstructible_rightDerivedLowerShriek_obj Λ f K.obj K.property

/-- The restricted derived lower shriek is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    boundedConstructibleLowerShriek Λ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)_!⟦Λ⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The exceptional inverse image `Rf^!` on module objects over `Λ` preserves bounded
constructible complexes. -/
lemma boundedConstructible_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : boundedConstructible (condensedRingObj Λ Y) K) :
    boundedConstructible (condensedRingObj Λ X) ((R(f)^!⟦Λ⟧).obj K) :=
  sorry

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the restriction of `R(f)^!⟦Λ⟧`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R(f)^!⟦Λ⟧)
    fun K ↦ boundedConstructible_rightDerivedUpperShriek_obj Λ f K.obj K.property

/-- The restricted exceptional inverse image is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperShriekCompatibility :
    boundedConstructibleUpperShriek Λ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)^!⟦Λ⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.rightDerivedUpperShriekAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek Λ f ⊣ boundedConstructibleUpperShriek Λ f :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction Λ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleLowerShriekCompatibility Λ f).symm
    (boundedConstructibleUpperShriekCompatibility Λ f).symm

end Shriek

/-! ### The derived tensor product and the derived hom -/

section TensorHom

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- The derived tensor product of module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedTensor_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hK : boundedConstructible (condensedRingObj Λ X) K)
    (hL : boundedConstructible (condensedRingObj Λ X) L) :
    boundedConstructible (condensedRingObj Λ X) (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj L) :=
  sorry

/-- The derived hom of module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedHom_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hK : boundedConstructible (condensedRingObj Λ X) K)
    (hL : boundedConstructible (condensedRingObj Λ X) L) :
    boundedConstructible (condensedRingObj Λ X) (((RHom(X)⟦Λ⟧).obj (op K)).obj L) :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded
constructible complexes: the restriction of `-⊗ᴸ-(X)⟦Λ⟧` in both variables. -/
noncomputable def boundedConstructibleTensor : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj -⊗ᴸ-(X)⟦Λ⟧)
    fun KL ↦ boundedConstructible_derivedTensor_obj Λ X KL.1.property KL.2.property)

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦Λ⟧ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the restriction of `RHom(X)⟦Λ⟧` in both variables. -/
noncomputable def boundedConstructibleHom : (Dᵇc(X)⟦Λ⟧)ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.op.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj RHom(X)⟦Λ⟧)
    fun KL ↦ boundedConstructible_derivedHom_obj Λ X KL.1.unop.property KL.2.property)

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility (K : Dᵇc(X)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X)⟦Λ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility (K : Dᵇc(X)⟦Λ⟧) :
    (boundedConstructibleHom Λ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X)⟦Λ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleHom]

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the restriction of `ProEtale.CondensedRing.derivedTensorHomAdjunction` along the
fully faithful inclusions. -/
noncomputable def boundedConstructibleTensorHomAdjunction (K : Dᵇc(X)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⊣ (boundedConstructibleHom Λ X).obj (op K) :=
  Adjunction.restrictFullyFaithful (derivedTensorHomAdjunction Λ K.obj)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleTensorObjCompatibility Λ K).symm
    (boundedConstructibleHomObjCompatibility Λ K).symm

end TensorHom

end AlgebraicGeometry.ProEtale.CondensedRing
