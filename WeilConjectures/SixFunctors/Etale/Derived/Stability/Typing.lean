/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix

/-!
# The typing rule: the operations on `Dctf` are restrictions of the ambient ones

Every operation of the six-functor formalism is defined on the ambient derived categories
`D(X_ét, Λ)`; the functors between the small categories `Dctf(X, Λ)` are *restrictions* of the
ambient ones, and that the restriction exists is a theorem (blueprint `rem-sf-typing-rule`,
`sk-rem-sf-typing-rule`). This file

* proves the general fact behind the typing rule: a functor into an ambient category restricts
  to a full subcategory (closed under isomorphisms) exactly when it carries every object into
  it, and the restriction is unique up to isomorphism
  (`CategoryTheory.ObjectProperty.exists_comp_ι_iso_iff`,
  `CategoryTheory.ObjectProperty.isoLiftOfCompιIso`);
* constructs the two restricted bifunctors of clause (ii) of `sk-thm-sf-ctf-stability`, the
  derived tensor product `Dctf × Dctf ⥤ Dctf` and the internal hom `Dctfᵒᵖ × Dctf ⥤ Dctf`
  (`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedTensor`,
  `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedHom`);
* proves the part of clause (vi) of `sk-thm-sf-ctf-stability` that concerns the restricted
  functor: `𝔻_X 𝔻_X K ≅ K` in `Dctf(X, Λ)` and `𝔻_X : Dctf(X, Λ)ᵒᵖ ⥤ Dctf(X, Λ)` is
  essentially surjective;
* states the typing rule: each restricted functor, followed by the inclusion, is the inclusion
  followed by the ambient operation (`AlgebraicGeometry.Etale.typingRule`).

## Implementation notes

The biduality isomorphism `K ≅ 𝔻_X 𝔻_X K` of
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` is only asserted to exist,
objectwise; it is not stated to be the natural double-dual map. Hence the restricted Verdier
dual is shown here to be essentially surjective with `𝔻_X 𝔻_X K ≅ K` for every `K`, which is
what the objectwise statement gives.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.ObjectProperty

variable {D E : Type*} [Category* D] [Category* E] (Q : ObjectProperty D)

/-- **Restrictions to a full subcategory are unique.** If `G : E ⥤ Q.FullSubcategory` followed
by the inclusion is isomorphic to `F`, then `G` is isomorphic to the lift of `F`, the inclusion
being fully faithful. -/
noncomputable def isoLiftOfCompιIso {F : E ⥤ D} (hF : ∀ X, Q (F.obj X))
    (G : E ⥤ Q.FullSubcategory) (e : G ⋙ Q.ι ≅ F) : G ≅ Q.lift F hF :=
  (Q.fullyFaithfulι.whiskeringRight E).preimageIso (e ≪≫ (Q.liftCompιIso F hF).symm)

/-- **A functor restricts to a full subcategory iff it carries every object into it.** For `Q`
closed under isomorphisms, `F : E ⥤ D` is isomorphic to a functor `G : E ⥤ Q.FullSubcategory`
followed by the inclusion exactly when every `F.obj X` satisfies `Q`. -/
lemma exists_comp_ι_iso_iff [Q.IsClosedUnderIsomorphisms] (F : E ⥤ D) :
    (∃ G : E ⥤ Q.FullSubcategory, Nonempty (G ⋙ Q.ι ≅ F)) ↔ ∀ X, Q (F.obj X) :=
  ⟨fun ⟨G, ⟨e⟩⟩ X ↦ Q.prop_of_iso (e.app X) (G.obj X).property,
    fun h ↦ ⟨Q.lift F h, ⟨Q.liftCompιIso F h⟩⟩⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### Clause (ii): the restricted bifunctors -/

section Bifunctors

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (ii): the restriction
`- ⊗ᴸ - : Dctf(X, Λ) × Dctf(X, Λ) ⥤ Dctf(X, Λ)` of the derived tensor product to the small
categories, written in curried form, for a finite coefficient ring `Λ`. -/
noncomputable def DerivedCategoryFiniteTor.derivedTensorUncurried (X : Scheme.{u}) :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ×
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    ((DerivedCategoryFiniteTor.ι _ X).prod (DerivedCategoryFiniteTor.ι _ X) ⋙
      Functor.uncurry.obj (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]))
    fun K ↦ constructibleFiniteTor_tensor Λ X K.1.property K.2.property

@[inherit_doc DerivedCategoryFiniteTor.derivedTensorUncurried]
noncomputable def DerivedCategoryFiniteTor.derivedTensor (X : Scheme.{u}) :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  Functor.curry.obj (DerivedCategoryFiniteTor.derivedTensorUncurried Λ X)

/-- The restricted derived tensor product, followed by the inclusion, is the derived tensor
product of the inclusions. -/
noncomputable def DerivedCategoryFiniteTor.derivedTensorCompιIso (X : Scheme.{u}) :
    Functor.uncurry.obj (DerivedCategoryFiniteTor.derivedTensor Λ X) ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
      (DerivedCategoryFiniteTor.ι _ X).prod (DerivedCategoryFiniteTor.ι _ X) ⋙
        Functor.uncurry.obj (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]) :=
  Functor.isoWhiskerRight (Functor.currying.counitIso.app
      (DerivedCategoryFiniteTor.derivedTensorUncurried Λ X)) _ ≪≫
    ObjectProperty.liftCompιIso _ _ _

/-- The internal hom of two objects of `Dctf(X, Λ)`, computed in the ambient derived category
`D(X_ét, Λ)`: the composite of the inclusions with `RHom(-, -)`. -/
noncomputable def DerivedCategoryFiniteTor.ambientDerivedHom (X : Scheme.{u}) :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ×
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategoryFiniteTor.ι _ X).op.prod (DerivedCategoryFiniteTor.ι _ X) ⋙
    Functor.uncurry.obj (RHom(X)[ModuleCat.{u + 1} Λ])

variable {k : Type u} [Field k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (ii): the restriction
`RHom(-, -) : Dctf(X, Λ)ᵒᵖ × Dctf(X, Λ) ⥤ Dctf(X, Λ)` of the internal hom to the small
categories, written in curried form, for `X` of finite type over a field `k` and a finite `Λ`
whose exponent is invertible on `X`. Both variables are arbitrary objects of `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom`). -/
noncomputable def DerivedCategoryFiniteTor.derivedHomUncurried :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ×
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ambientDerivedHom Λ X)
    fun K ↦ constructibleFiniteTor_derivedHom Λ aX K.1.unop.property K.2.property

@[inherit_doc DerivedCategoryFiniteTor.derivedHomUncurried]
noncomputable def DerivedCategoryFiniteTor.derivedHom :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
        DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  Functor.curry.obj (DerivedCategoryFiniteTor.derivedHomUncurried Λ aX)

/-- The restricted internal hom, followed by the inclusion, is the internal hom of the
inclusions. -/
noncomputable def DerivedCategoryFiniteTor.derivedHomCompιIso :
    Functor.uncurry.obj (DerivedCategoryFiniteTor.derivedHom Λ aX) ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
      (DerivedCategoryFiniteTor.ι _ X).op.prod (DerivedCategoryFiniteTor.ι _ X) ⋙
        Functor.uncurry.obj (RHom(X)[ModuleCat.{u + 1} Λ]) :=
  Functor.isoWhiskerRight (Functor.currying.counitIso.app
      (DerivedCategoryFiniteTor.derivedHomUncurried Λ aX)) _ ≪≫
    ObjectProperty.liftCompιIso _ _ _ ≪≫ Iso.refl _

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (ii): for `K ∈ Dctf(X, Λ)`, the restriction
`K ⊗ᴸ - : Dctf(X, Λ) ⥤ Dctf(X, Λ)` of the derived tensor product with `K`. -/
noncomputable def DerivedCategoryFiniteTor.tensorLeft
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.liftFullSubcategory _ _ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K.obj)
    fun _ hM ↦ constructibleFiniteTor_tensor Λ X K.property hM

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (ii): for `K ∈ Dctf(X, Λ)`, the restriction
`RHom(K, -) : Dctf(X, Λ) ⥤ Dctf(X, Λ)` of the internal hom out of `K`. -/
noncomputable def DerivedCategoryFiniteTor.homLeft
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.liftFullSubcategory _ _ ((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K.obj))
    fun _ hM ↦ constructibleFiniteTor_derivedHom Λ aX K.property hM

/-- The tensor-hom adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` restricts to the small category
`Dctf(X, Λ)`, with the unit and counit of
`AlgebraicGeometry.Etale.derivedTensorHomAdjunction`. -/
noncomputable def DerivedCategoryFiniteTor.tensorHomAdjunction
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    DerivedCategoryFiniteTor.tensorLeft Λ K ⊣ DerivedCategoryFiniteTor.homLeft Λ aX K :=
  (derivedTensorHomAdjunction _ K.obj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
    (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm

end Bifunctors

/-! ### Clause (vi): the restricted Verdier dual -/

section VerdierDual

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasCompactification aX]

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (vi): for `X` separated of finite type over a
field `k` and a finite `Λ` whose exponent is invertible on `k`, every object `K` of the small
category `Dctf(X, Λ)` is isomorphic, inside `Dctf(X, Λ)`, to its double Verdier dual
`𝔻_X 𝔻_X K`, the Verdier dual being restricted to `Dctf(X, Λ)` by
`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem DerivedCategoryFiniteTor.nonempty_iso_verdierDual_verdierDual
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X) :
    Nonempty (K ≅ (DerivedCategoryFiniteTor.verdierDual _ aX
      fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK).obj
        (op ((DerivedCategoryFiniteTor.verdierDual _ aX
          fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK).obj (op K)))) :=
  ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (Etale.nonempty_iso_verdierDual_verdierDual Λ aX K.property).some⟩

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (vi): the restricted Verdier dual
`𝔻_X : Dctf(X, Λ)ᵒᵖ ⥤ Dctf(X, Λ)` is essentially surjective, every `K` being the dual of
`𝔻_X K`. -/
theorem DerivedCategoryFiniteTor.essSurj_verdierDual :
    (DerivedCategoryFiniteTor.verdierDual (ModuleCat.{u + 1} Λ) aX
      fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK).EssSurj :=
  ⟨fun K ↦ ⟨_, ⟨(DerivedCategoryFiniteTor.nonempty_iso_verdierDual_verdierDual Λ aX K).some.symm⟩⟩⟩

end VerdierDual

/-! ### The typing rule -/

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aX] [HasCompactification aX] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f] [QuasiCompact f]
  [HasCompactification f]

/-- Blueprint `rem-sf-typing-rule`: The typing rule of this section.

Every operation is defined on the ambient derived categories `D(-_ét, Λ)`, and its version on
the small categories `Dctf(-, Λ)` is its restriction: for a finite `Λ` whose exponent is
invertible on `k` and a separated morphism `f : X ⟶ Y` of schemes of finite type over `k`,
with `X` separated over `k`, each of the functors `Lf^*`, `Rf_*`, `Rf_!`, `Rf^!`, `𝔻_X`,
`- ⊗ᴸ -` and `RHom(-, -)` between the small categories, followed by the inclusion, is
isomorphic to the inclusion followed by the ambient operation. By
`CategoryTheory.ObjectProperty.isoLiftOfCompιIso` a functor between the small categories with
this property is unique up to isomorphism, and by
`CategoryTheory.ObjectProperty.exists_comp_ι_iso_iff` its existence is equivalent to the
preservation statements of `sk-thm-sf-ctf-stability`. -/
theorem typingRule :
    Nonempty (DerivedCategoryFiniteTor.leftDerivedUpperStar (ModuleCat.{u + 1} Λ) f ⋙
        DerivedCategoryFiniteTor.ι _ X ≅
      DerivedCategoryFiniteTor.ι _ Y ⋙ L((f)^*[ModuleCat.{u + 1} Λ])) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerStar Λ aX aY f hf ⋙
        DerivedCategoryFiniteTor.ι _ Y ≅
      DerivedCategoryFiniteTor.ι _ X ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⋙
        DerivedCategoryFiniteTor.ι _ Y ≅
      DerivedCategoryFiniteTor.ι _ X ⋙ R(f)_![ModuleCat.{u + 1} Λ]) ∧
    Nonempty (DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f ⋙
        DerivedCategoryFiniteTor.ι _ X ≅
      DerivedCategoryFiniteTor.ι _ Y ⋙ R(f)^![ModuleCat.{u + 1} Λ]) ∧
    Nonempty (DerivedCategoryFiniteTor.verdierDual (ModuleCat.{u + 1} Λ) aX
          (fun _ hK ↦ constructibleFiniteTor_verdierDual Λ aX hK) ⋙
        DerivedCategoryFiniteTor.ι _ X ≅
      (DerivedCategoryFiniteTor.ι _ X).op ⋙ verdierDual (ModuleCat.{u + 1} Λ) aX) ∧
    Nonempty (Functor.uncurry.obj (DerivedCategoryFiniteTor.derivedTensor Λ X) ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
      (DerivedCategoryFiniteTor.ι _ X).prod (DerivedCategoryFiniteTor.ι _ X) ⋙
        Functor.uncurry.obj (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ])) ∧
    Nonempty (Functor.uncurry.obj (DerivedCategoryFiniteTor.derivedHom Λ aX) ⋙
        DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ≅
      (DerivedCategoryFiniteTor.ι _ X).op.prod (DerivedCategoryFiniteTor.ι _ X) ⋙
        Functor.uncurry.obj (RHom(X)[ModuleCat.{u + 1} Λ])) :=
  ⟨⟨ObjectProperty.liftCompιIso _ _ _⟩, ⟨ObjectProperty.liftCompιIso _ _ _⟩,
    ⟨ObjectProperty.liftCompιIso _ _ _⟩, ⟨ObjectProperty.liftCompιIso _ _ _⟩,
    ⟨ObjectProperty.liftCompιIso _ _ _⟩, ⟨DerivedCategoryFiniteTor.derivedTensorCompιIso Λ X⟩,
    ⟨DerivedCategoryFiniteTor.derivedHomCompιIso Λ aX⟩⟩

end Etale

end AlgebraicGeometry
