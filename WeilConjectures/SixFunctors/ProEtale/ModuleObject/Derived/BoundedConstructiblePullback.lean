/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# Coherence of the derived pullbacks on bounded constructible complexes

Let `Λ` be a commutative condensed ring, `ℓ` a prime and `k` a field of characteristic `p ≠ ℓ`.
For separated `k`-schemes of finite type, this file defines the identity isomorphisms
`L(𝟙 X)^* ≅ 𝟭` and `R(𝟙 X)_* ≅ 𝟭` of the derived pullback and pushforward on the bounded
constructible derived categories `Dᵇc(X)⟦Λ⟧`, and shows that the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`ProEtale.CondensedRing.boundedConstructibleUpperStarComp`) satisfy,
together with the identity isomorphisms, the associativity and unit laws.

The identity isomorphism of the pullback is the restriction of the identity isomorphism
`ProEtale.CondensedRing.leftDerivedUpperStarId` of the derived pullback on `D(Mod_{Λ_X})` along
the fully faithful inclusion, as for the composition isomorphisms, so that the laws are those of
the derived pullbacks (`ProEtale.CondensedRing.leftDerivedUpperStarComp_assoc_app`,
`ProEtale.CondensedRing.leftDerivedUpperStarComp_id_left_app`,
`ProEtale.CondensedRing.leftDerivedUpperStarComp_id_right_app`). The identity isomorphism of the
pushforward is its conjugate under the adjunction `L(𝟙 X)^* ⊣ R(𝟙 X)_*`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperStarId`: `L(𝟙 X)^* ≅ 𝟭`.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarId`: `R(𝟙 X)_* ≅ 𝟭`.

## Main results

- `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_assoc_app`: the associativity law.
- `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_id_left_app`,
  `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_id_right_app`: the unit laws.
- `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_cocycle_aux`,
  `CategoryTheory.PullbackFamily.transport`, `CategoryTheory.PullbackFamily.commute`: consequences
  of the laws for iterated coefficient maps `LΦ^* K ⟶ K` along endomorphisms, used for the iterates
  of Weil structures and the Frobenius transport of their stalks.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.PullbackFamily

/-! ### Families of pullback functors indexed by morphisms

The lemmas of this section concern families `U` of functors indexed by the morphisms between two
objects `W` and `X` of a category, together with composition isomorphisms
`U (a ≫ b) ≅ U b ⋙ U a` and identity isomorphisms `U (𝟙) ≅ 𝟭`, such as the derived pullbacks on
bounded constructible complexes. Stating them for an abstract family keeps the morphisms and the
functors opaque, which makes the computations cheap. -/

section Transport

variable {𝒞 : Type*} [Category 𝒞] {W X : 𝒞} {DW DX : Type*} [Category DW] [Category DX]
  (UWW : (W ⟶ W) → DW ⥤ DW) (UWX : (W ⟶ X) → DX ⥤ DW) (UXX : (X ⟶ X) → DX ⥤ DX)
  (cWW : ∀ (a : W ⟶ W) (b : W ⟶ X), UWX (a ≫ b) ≅ UWX b ⋙ UWW a)
  (cWX : ∀ (a : W ⟶ X) (b : X ⟶ X), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
  (cXX : ∀ (a b : X ⟶ X), UXX (a ≫ b) ≅ UXX b ⋙ UXX a)
  (ιW : UWW (𝟙 W) ≅ 𝟭 DW)

include cWW ιW in
/-- The inverse of the composition isomorphism `U (𝟙 ≫ b) ≅ U b ⋙ U 𝟙` is the identity isomorphism
`U 𝟙 ≅ 𝟭`, up to `𝟙 ≫ b = b`, given the left unit law. -/
lemma inv_app_id_left
    (hidl : ∀ (b : W ⟶ X) (K : DX), (cWW (𝟙 W) b).hom.app K ≫ ιW.hom.app ((UWX b).obj K) =
      eqToHom (show (UWX (𝟙 W ≫ b)).obj K = _ by rw [Category.id_comp]; rfl))
    (b : W ⟶ X) (K : DX) :
    (cWW (𝟙 W) b).inv.app K =
      ιW.hom.app ((UWX b).obj K) ≫ eqToHom (by rw [Category.id_comp]; rfl) := by
  rw [← cancel_epi ((cWW (𝟙 W) b).hom.app K), Iso.hom_inv_id_app, reassoc_of% (hidl b K)]
  simp

end Transport

section Commute

variable {𝒞 : Type*} [Category 𝒞] {X : 𝒞} {DX : Type*} [Category DX]
  (UXX : (X ⟶ X) → DX ⥤ DX) (cXX : ∀ (a b : X ⟶ X), UXX (a ≫ b) ≅ UXX b ⋙ UXX a)
  (ιX : UXX (𝟙 X) ≅ 𝟭 DX)

end Commute

end CategoryTheory.PullbackFamily

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The identity isomorphisms -/

section Id

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on bounded constructible
complexes of module objects over `Λ`: the restriction of
`ProEtale.CondensedRing.leftDerivedUpperStarId` along the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarId :
    boundedConstructibleUpperStar Λ ℓ (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (𝟙 X) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarId Λ X.left) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- On the ambient derived category, the identity isomorphism of the derived pullback on bounded
constructible complexes is `ProEtale.CondensedRing.leftDerivedUpperStarId`. -/
@[simp]
lemma boundedConstructibleUpperStarId_hom_app_hom (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarId Λ ℓ X).hom.app K).hom =
      (leftDerivedUpperStarId Λ X.left).hom.app K.obj := by
  simp only [Functor.id_obj, boundedConstructibleUpperStarId, Functor.whiskeringRight_obj_obj,
    Over.id_left, boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom, Iso.refl_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.FullyFaithful.preimage_comp, NatTrans.comp_app,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.id_app, Functor.comp_obj,
    ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  exact Category.id_comp _

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the derived pushforward on bounded constructible
complexes of module objects over `ℚ̲̄_ℓ`: the conjugate of
`ProEtale.CondensedRing.boundedConstructibleUpperStarId` under the adjunctions
`L(𝟙 X)^* ⊣ R(𝟙 X)_*` and `𝟭 ⊣ 𝟭`. -/
noncomputable def boundedConstructibleLowerStarId :
    boundedConstructibleLowerStar ℓ (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X)) Adjunction.id
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).symm

end Id

/-! ### The laws -/

section Laws

variable {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

@[simp]
lemma boundedConstructibleUpperStar_map_hom (f : X ⟶ Y) {K L : Dᵇc(Y.left)⟦Λ⟧} (φ : K ⟶ L) :
    ((boundedConstructibleUpperStar Λ ℓ f).map φ).hom = L((f.left)^*⟦Λ⟧).map φ.hom :=
  rfl

@[simp]
lemma boundedConstructibleUpperStar_obj_obj (f : X ⟶ Y) (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStar Λ ℓ f).obj K).obj = L((f.left)^*⟦Λ⟧).obj K.obj :=
  rfl

/-- On the ambient derived category, the composition isomorphism of the derived pullbacks on
bounded constructible complexes is `ProEtale.CondensedRing.leftDerivedUpperStarComp`. -/
@[simp]
lemma boundedConstructibleUpperStarComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Dᵇc(Z.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarComp Λ ℓ f g).hom.app K).hom =
      (leftDerivedUpperStarComp Λ f.left g.left).hom.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- **Associativity** of the composition isomorphisms of the derived pullbacks on bounded
constructible complexes: the two ways of identifying `L(f ≫ g ≫ h)^*` with
`Lh^* ⋙ Lg^* ⋙ Lf^*` agree. -/
lemma boundedConstructibleUpperStarComp_assoc_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ (f ≫ g) h).hom.app K ≫
        (boundedConstructibleUpperStarComp Λ ℓ f g).hom.app
          ((boundedConstructibleUpperStar Λ ℓ h).obj K) =
      eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ f (g ≫ h)).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ f).map
          ((boundedConstructibleUpperStarComp Λ ℓ g h).hom.app K) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStar_map_hom, ObjectProperty.eqToHom_hom]
  exact leftDerivedUpperStarComp_assoc_app Λ f.left g.left h.left K.obj

/-- **Left unit law** for the composition isomorphisms of the derived pullbacks on bounded
constructible complexes. -/
lemma boundedConstructibleUpperStarComp_id_left_app (g : X ⟶ Y) (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ (𝟙 X) g).hom.app K ≫
        (boundedConstructibleUpperStarId Λ ℓ X).hom.app
          ((boundedConstructibleUpperStar Λ ℓ g).obj K) =
      eqToHom (by rw [Category.id_comp]; rfl) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStarId_hom_app_hom, ObjectProperty.eqToHom_hom]
  exact leftDerivedUpperStarComp_id_left_app Λ g.left K.obj

/-- **Right unit law** for the composition isomorphisms of the derived pullbacks on bounded
constructible complexes. -/
lemma boundedConstructibleUpperStarComp_id_right_app (f : X ⟶ Y) (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ f (𝟙 Y)).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ f).map
          ((boundedConstructibleUpperStarId Λ ℓ Y).hom.app K) =
      eqToHom (by rw [Category.comp_id]; rfl) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStarId_hom_app_hom, boundedConstructibleUpperStar_map_hom,
    ObjectProperty.eqToHom_hom]
  exact leftDerivedUpperStarComp_id_right_app Λ f.left K.obj

/-! ### Iterated coefficient maps along endomorphisms -/

/-- The unit step for iterated coefficient maps along endomorphisms: for endomorphisms `P = 𝟙 X`
and `R` of `X` and a map `ψ_R : LR^* K ⟶ K`, the composite
`LR^* K ≅ L(P ≫ R)^* K ≅ LP^* LR^* K ⟶ LP^* K ≅ K` of `LP^* ψ_R` and the identity isomorphism
`L(𝟙 X)^* ≅ 𝟭` is `ψ_R`. -/
lemma boundedConstructibleUpperStarComp_id_aux {P R : X ⟶ X} (hP : P = 𝟙 X) (e : R = P ≫ R)
    {K : Dᵇc(X.left)⟦Λ⟧} (ψR : (boundedConstructibleUpperStar Λ ℓ R).obj K ⟶ K) :
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ R).obj K = _ by rw [← e]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ P R).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ P).map ψR ≫ eqToHom (by rw [hP]) ≫
        (boundedConstructibleUpperStarId Λ ℓ X).hom.app K = ψR := by
  subst hP
  have hn := (boundedConstructibleUpperStarId Λ ℓ X).hom.naturality ψR
  have hl := boundedConstructibleUpperStarComp_id_left_app Λ ℓ R K
  simp only [Functor.id_map] at hn
  simp only [eqToHom_refl, Category.id_comp]
  rw [hn, reassoc_of% hl]
  simp

/-- The unit step for iterated coefficient maps along endomorphisms, on the right: for
endomorphisms `Φ` and `P = 𝟙 X` of `X` and a map `ψ : LΦ^* K ⟶ K`, the composite
`LΦ^* K ≅ L(Φ ≫ P)^* K ≅ LΦ^* LP^* K ≅ LΦ^* K ⟶ K` of the identity isomorphism
`L(𝟙 X)^* ≅ 𝟭` and `ψ` is `ψ`. -/
lemma boundedConstructibleUpperStarComp_id_right_aux {Φ P : X ⟶ X} (hP : P = 𝟙 X)
    (e : Φ = Φ ≫ P) {K : Dᵇc(X.left)⟦Λ⟧} (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) :
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ Φ).obj K = _ by rw [← e]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ Φ P).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ Φ).map (eqToHom (by rw [hP]) ≫
          (boundedConstructibleUpperStarId Λ ℓ X).hom.app K) ≫ ψ = ψ := by
  subst hP
  have hr := boundedConstructibleUpperStarComp_id_right_app Λ ℓ Φ K
  simp only [eqToHom_refl, Category.id_comp]
  rw [reassoc_of% hr]
  simp

end Laws

end AlgebraicGeometry.ProEtale.CondensedRing
