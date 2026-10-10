/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.UpperShriek

/-!

# The six functors on bounded constructible module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime. For a scheme `X`, the bounded constructible derived category
`D_cons(X_proét, ℚ̄_ℓ)` of module objects over the coefficient ring object `ℚ̄_ℓ,X` is the full
subcategory `ProEtale.BoundedConstructible (padicAlgClSheaf X ℓ)` of `D(Mod_{ℚ̄_ℓ,X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦ℚ̄_ℓ⟧`. This file restricts the six functors on `D(Mod_{ℚ̄_ℓ,X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived` to these full
subcategories:

| functor | restriction | hypotheses |
| --- | --- | --- |
| `Lf^* = L((f)^*⟦ℚ̄_ℓ⟧)` | `boundedConstructibleUpperStar` | `X`, `Y` noetherian |
| `Rf_* = R((f)_*⟦ℚ̄_ℓ⟧)` | `boundedConstructibleLowerStar` | and `f` of finite type |
| `Rf_! = R(f)_!⟦ℚ̄_ℓ⟧` | `boundedConstructibleLowerShriek` | and `HasCompactification f` |
| `j_! = D((j)_!open⟦ℚ̄_ℓ⟧)` | `boundedConstructibleOpenImmersionLowerShriek` | `j` open immersion |
| `Rf^! = R(f)^!⟦ℚ̄_ℓ⟧` | `boundedConstructibleUpperShriek` | and `HasCompactification f` |
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
i.e. schemes of finite type over a regular base of dimension `≤ 1` on which `ℓ` is invertible.
The hypotheses are to be strengthened when the statements are proved.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The bounded constructible derived category `D_cons(X_proét, ℚ̄_ℓ)` of module objects over
`ℚ̄_ℓ,X`. -/
scoped notation "Dᵇc(" X ")⟦ℚ̄_" ℓ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (padicAlgClSheaf X ℓ)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [NoetherianSpace X] [NoetherianSpace Y]

/-- The derived pullback `Lf^*` on module objects over `ℚ̄_ℓ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf Y ℓ) K) :
    boundedConstructible (padicAlgClSheaf X ℓ) ((L((f)^*⟦ℚ̄_ℓ⟧)).obj K) :=
  sorry

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded constructible
complexes: the restriction of `L((f)^*⟦ℚ̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f)^*⟦ℚ̄_ℓ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj ℓ f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f)^*⟦ℚ̄_ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.PadicAlgClRing.leftDerivedUpperStarComp` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Scheme.{u}} [NoetherianSpace Z]
    (g : Y ⟶ Z) :
    boundedConstructibleUpperStar ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar ℓ g ⋙ boundedConstructibleUpperStar ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility ℓ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp ℓ f g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility ℓ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

variable [LocallyOfFiniteType f] [QuasiCompact f]

/-- The derived pushforward `Rf_*` on module objects over `ℚ̄_ℓ` along a morphism of finite
type preserves bounded constructible complexes. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K) :
    boundedConstructible (padicAlgClSheaf Y ℓ) ((R((f)_*⟦ℚ̄_ℓ⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦ℚ̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleLowerStar : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f)_*⟦ℚ̄_ℓ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f)_*⟦ℚ̄_ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.PadicAlgClRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar ℓ f ⊣ boundedConstructibleLowerStar ℓ f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction ℓ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ f).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [NoetherianSpace U]
  [NoetherianSpace X]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `ℚ̄_ℓ`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicAlgClSheaf U ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf U ℓ) K) :
    boundedConstructible (padicAlgClSheaf X ℓ) ((D((j)_!open⟦ℚ̄_ℓ⟧)).obj K) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦ℚ̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek :
    Dᵇc(U)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j)_!open⟦ℚ̄_ℓ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj ℓ j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j)_!open⟦ℚ̄_ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.PadicAlgClRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦ℚ̄_ℓ⟧)` being identified with the
derived pullback `L((j)^*⟦ℚ̄_ℓ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek ℓ j ⊣ boundedConstructibleUpperStar ℓ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion ℓ j).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility ℓ j).symm
    (boundedConstructibleUpperStarCompatibility ℓ j).symm

end OpenImmersion

/-! ### The exceptional functors -/

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [NoetherianSpace X] [NoetherianSpace Y]

/-- The derived lower shriek `Rf_!` on module objects over `ℚ̄_ℓ` preserves bounded
constructible complexes. -/
lemma boundedConstructible_rightDerivedLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K) :
    boundedConstructible (padicAlgClSheaf Y ℓ) ((R(f)_!⟦ℚ̄_ℓ⟧).obj K) :=
  sorry

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧` on bounded constructible
complexes: the restriction of `R(f)_!⟦ℚ̄_ℓ⟧`. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R(f)_!⟦ℚ̄_ℓ⟧)
    fun K ↦ boundedConstructible_rightDerivedLowerShriek_obj ℓ f K.obj K.property

/-- The restricted derived lower shriek is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)_!⟦ℚ̄_ℓ⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The exceptional inverse image `Rf^!` on module objects over `ℚ̄_ℓ` preserves bounded
constructible complexes. -/
lemma boundedConstructible_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf Y ℓ) K) :
    boundedConstructible (padicAlgClSheaf X ℓ) ((R(f)^!⟦ℚ̄_ℓ⟧).obj K) :=
  sorry

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded constructible
complexes: the restriction of `R(f)^!⟦ℚ̄_ℓ⟧`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R(f)^!⟦ℚ̄_ℓ⟧)
    fun K ↦ boundedConstructible_rightDerivedUpperShriek_obj ℓ f K.obj K.property

/-- The restricted exceptional inverse image is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperShriekCompatibility :
    boundedConstructibleUpperShriek ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)^!⟦ℚ̄_ℓ⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the restriction of
`ProEtale.PadicAlgClRing.rightDerivedUpperShriekAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek ℓ f ⊣ boundedConstructibleUpperShriek ℓ f :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction ℓ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleLowerShriekCompatibility ℓ f).symm
    (boundedConstructibleUpperShriekCompatibility ℓ f).symm

end Shriek

/-! ### The derived tensor product and the derived hom -/

section TensorHom

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- The derived tensor product of module objects over `ℚ̄_ℓ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedTensor_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))}
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K)
    (hL : boundedConstructible (padicAlgClSheaf X ℓ) L) :
    boundedConstructible (padicAlgClSheaf X ℓ) (((-⊗ᴸ-(X)⟦ℚ̄_ℓ⟧).obj K).obj L) :=
  sorry

/-- The derived hom of module objects over `ℚ̄_ℓ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedHom_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))}
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K)
    (hL : boundedConstructible (padicAlgClSheaf X ℓ) L) :
    boundedConstructible (padicAlgClSheaf X ℓ) (((RHom(X)⟦ℚ̄_ℓ⟧).obj (op K)).obj L) :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded
constructible complexes: the restriction of `-⊗ᴸ-(X)⟦ℚ̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleTensor : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj -⊗ᴸ-(X)⟦ℚ̄_ℓ⟧)
    fun KL ↦ boundedConstructible_derivedTensor_obj ℓ X KL.1.property KL.2.property)

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦ℚ̄_ℓ⟧ᵒᵖ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` on bounded
constructible complexes: the restriction of `RHom(X)⟦ℚ̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleHom : (Dᵇc(X)⟦ℚ̄_ℓ⟧)ᵒᵖ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.op.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj RHom(X)⟦ℚ̄_ℓ⟧)
    fun KL ↦ boundedConstructible_derivedHom_obj ℓ X KL.1.unop.property KL.2.property)

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̄_ℓ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility (K : Dᵇc(X)⟦ℚ̄_ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X)⟦ℚ̄_ℓ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̄_ℓ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility (K : Dᵇc(X)⟦ℚ̄_ℓ⟧) :
    (boundedConstructibleHom ℓ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X)⟦ℚ̄_ℓ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleHom]

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̄_ℓ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the restriction of `ProEtale.PadicAlgClRing.derivedTensorHomAdjunction` along the
fully faithful inclusions. -/
noncomputable def boundedConstructibleTensorHomAdjunction (K : Dᵇc(X)⟦ℚ̄_ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⊣ (boundedConstructibleHom ℓ X).obj (op K) :=
  Adjunction.restrictFullyFaithful (derivedTensorHomAdjunction ℓ K.obj)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleTensorObjCompatibility ℓ K).symm
    (boundedConstructibleHomObjCompatibility ℓ K).symm

end TensorHom

end AlgebraicGeometry.ProEtale.PadicAlgClRing
