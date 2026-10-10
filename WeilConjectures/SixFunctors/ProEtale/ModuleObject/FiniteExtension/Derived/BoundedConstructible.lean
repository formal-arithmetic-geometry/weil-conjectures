/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.UpperShriek

/-!

# The six functors on bounded constructible module objects over `C(-, T)`

Let `T` be a commutative topological ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, A_X(T))` of module objects over the coefficient ring object
`A_X(T) = C(-, T)` is the full subcategory
`ProEtale.BoundedConstructible (continuousMapRingObj T X)` of `D(Mod_{A_X(T)})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦T⟧`. This file restricts the six functors on `D(Mod_{A_X(T)})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived` to these full
subcategories:

| functor | restriction | hypotheses |
| --- | --- | --- |
| `Lf^* = L((f)^*⟦T⟧)` | `boundedConstructibleUpperStar` | `X`, `Y` noetherian |
| `Rf_* = R((f)_*⟦T⟧)` | `boundedConstructibleLowerStar` | and `f` of finite type |
| `Rf_! = R(f)_!⟦T⟧` | `boundedConstructibleLowerShriek` | and `HasCompactification f` |
| `j_! = D((j)_!open⟦T⟧)` | `boundedConstructibleOpenImmersionLowerShriek` | `j` an open immersion |
| `Rf^! = R(f)^!⟦T⟧` | `boundedConstructibleUpperShriek` | and `HasCompactification f` |
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
and for all six functors the coefficient ring `T` should be `𝒪_E` or `E` for a finite extension
`E` of `ℚ_ℓ`. The hypotheses are to be strengthened when the statements are proved.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The bounded constructible derived category `D_cons(X_proét, A_X(T))` of module objects over
`A_X(T) = C(-, T)`. -/
scoped notation "Dᵇc(" X ")⟦" T "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (continuousMapRingObj T X)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [NoetherianSpace X] [NoetherianSpace Y]

/-- The derived pullback `Lf^*` on module objects over `C(-, T)` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (continuousMapRingObj T Y)))
    (hK : boundedConstructible (continuousMapRingObj T Y) K) :
    boundedConstructible (continuousMapRingObj T X) ((L((f)^*⟦T⟧)).obj K) :=
  sorry

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦T⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f)^*⟦T⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj T f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar T f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f)^*⟦T⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.ContinuousMapRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Scheme.{u}} [NoetherianSpace Z]
    (g : Y ⟶ Z) :
    boundedConstructibleUpperStar T (f ≫ g) ≅
      boundedConstructibleUpperStar T g ⋙ boundedConstructibleUpperStar T f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility T (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp T f g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility T g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility T f).symm ≪≫
      (Functor.associator _ _ _).symm)

variable [LocallyOfFiniteType f] [QuasiCompact f]

/-- The derived pushforward `Rf_*` on module objects over `C(-, T)` along a morphism of finite
type preserves bounded constructible complexes. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)))
    (hK : boundedConstructible (continuousMapRingObj T X) K) :
    boundedConstructible (continuousMapRingObj T Y) ((R((f)_*⟦T⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y)⟦T⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦T⟧)`. -/
noncomputable def boundedConstructibleLowerStar : Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y)⟦T⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f)_*⟦T⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj T f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar T f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f)_*⟦T⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.ContinuousMapRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar T f ⊣ boundedConstructibleLowerStar T f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction T f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility T f).symm
    (boundedConstructibleLowerStarCompatibility T f).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [NoetherianSpace U]
  [NoetherianSpace X]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `C(-, T)`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (continuousMapRingObj T U)))
    (hK : boundedConstructible (continuousMapRingObj T U) K) :
    boundedConstructible (continuousMapRingObj T X) ((D((j)_!open⟦T⟧)).obj K) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦T⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j)_!open⟦T⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj T j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek T j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j)_!open⟦T⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.ContinuousMapRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦T⟧)` being identified with the
derived pullback `L((j)^*⟦T⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek T j ⊣ boundedConstructibleUpperStar T j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction T j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion T j).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility T j).symm
    (boundedConstructibleUpperStarCompatibility T j).symm

end OpenImmersion

/-! ### The exceptional functors -/

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [NoetherianSpace X] [NoetherianSpace Y]

/-- The derived lower shriek `Rf_!` on module objects over `C(-, T)` preserves bounded
constructible complexes. -/
lemma boundedConstructible_rightDerivedLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)))
    (hK : boundedConstructible (continuousMapRingObj T X) K) :
    boundedConstructible (continuousMapRingObj T Y) ((R(f)_!⟦T⟧).obj K) :=
  sorry

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y)⟦T⟧` on bounded constructible complexes:
the restriction of `R(f)_!⟦T⟧`. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y)⟦T⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R(f)_!⟦T⟧)
    fun K ↦ boundedConstructible_rightDerivedLowerShriek_obj T f K.obj K.property

/-- The restricted derived lower shriek is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    boundedConstructibleLowerShriek T f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)_!⟦T⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The exceptional inverse image `Rf^!` on module objects over `C(-, T)` preserves bounded
constructible complexes. -/
lemma boundedConstructible_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (continuousMapRingObj T Y)))
    (hK : boundedConstructible (continuousMapRingObj T Y) K) :
    boundedConstructible (continuousMapRingObj T X) ((R(f)^!⟦T⟧).obj K) :=
  sorry

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧` on bounded constructible
complexes: the restriction of `R(f)^!⟦T⟧`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R(f)^!⟦T⟧)
    fun K ↦ boundedConstructible_rightDerivedUpperShriek_obj T f K.obj K.property

/-- The restricted exceptional inverse image is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperShriekCompatibility :
    boundedConstructibleUpperShriek T f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f)^!⟦T⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the restriction of
`ProEtale.ContinuousMapRing.rightDerivedUpperShriekAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek T f ⊣ boundedConstructibleUpperShriek T f :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction T f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleLowerShriekCompatibility T f).symm
    (boundedConstructibleUpperShriekCompatibility T f).symm

end Shriek

/-! ### The derived tensor product and the derived hom -/

section TensorHom

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- The derived tensor product of module objects over `C(-, T)` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedTensor_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X))}
    (hK : boundedConstructible (continuousMapRingObj T X) K)
    (hL : boundedConstructible (continuousMapRingObj T X) L) :
    boundedConstructible (continuousMapRingObj T X) (((-⊗ᴸ-(X)⟦T⟧).obj K).obj L) :=
  sorry

/-- The derived hom of module objects over `C(-, T)` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedHom_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X))}
    (hK : boundedConstructible (continuousMapRingObj T X) K)
    (hL : boundedConstructible (continuousMapRingObj T X) L) :
    boundedConstructible (continuousMapRingObj T X) (((RHom(X)⟦T⟧).obj (op K)).obj L) :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧` on bounded
constructible complexes: the restriction of `-⊗ᴸ-(X)⟦T⟧` in both variables. -/
noncomputable def boundedConstructibleTensor : Dᵇc(X)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj -⊗ᴸ-(X)⟦T⟧)
    fun KL ↦ boundedConstructible_derivedTensor_obj T X KL.1.property KL.2.property)

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦T⟧ᵒᵖ ⥤ Dᵇc(X)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧` on bounded constructible
complexes: the restriction of `RHom(X)⟦T⟧` in both variables. -/
noncomputable def boundedConstructibleHom : (Dᵇc(X)⟦T⟧)ᵒᵖ ⥤ Dᵇc(X)⟦T⟧ ⥤ Dᵇc(X)⟦T⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.op.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj RHom(X)⟦T⟧)
    fun KL ↦ boundedConstructible_derivedHom_obj T X KL.1.unop.property KL.2.property)

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦T⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility (K : Dᵇc(X)⟦T⟧) :
    (boundedConstructibleTensor T X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X)⟦T⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦T⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility (K : Dᵇc(X)⟦T⟧) :
    (boundedConstructibleHom T X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X)⟦T⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleHom]

/-- For a fixed `K ∈ Dᵇc(X)⟦T⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the restriction of `ProEtale.ContinuousMapRing.derivedTensorHomAdjunction` along the
fully faithful inclusions. -/
noncomputable def boundedConstructibleTensorHomAdjunction (K : Dᵇc(X)⟦T⟧) :
    (boundedConstructibleTensor T X).obj K ⊣ (boundedConstructibleHom T X).obj (op K) :=
  Adjunction.restrictFullyFaithful (derivedTensorHomAdjunction T K.obj)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleTensorObjCompatibility T K).symm
    (boundedConstructibleHomObjCompatibility T K).symm

end TensorHom

end AlgebraicGeometry.ProEtale.ContinuousMapRing
