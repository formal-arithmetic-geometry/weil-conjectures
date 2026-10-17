/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange

/-!
# Products of Thom classes

Let `i₁ : Z₁ ⟶ U` and `i₂ : Z₂ ⟶ U` be closed immersions meeting in `i : Z ⟶ U`, and let
`α ∈ H_{Z₁}(U, L₁)`, `β ∈ H_{Z₂}(U, L₂)` be classes with supports, `L₂` invertible. Call a class
a *Thom class* if its adjoint `Λ_Z ⟶ Ri^! L` (`AlgebraicGeometry.Etale.supportedTranspose`) is
an isomorphism. If `α` is a Thom class and the restriction of `β` to `Z₁` is a Thom class of
`Z ⊂ Z₁`, then the cup product with supports `α ∪ β` is a Thom class of `Z ⊂ U`
(`AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`).

This is the multiplicativity of fundamental classes used to compute the class of the zero
section of `𝔸^c` as the product of the Kummer boundaries of the coordinates (`sk-prop-an`).

The argument characterises Thom classes by a universal property which only involves the
*forget-supports* morphism `χ : Ri_! Λ_Z ⟶ L` of the class: the adjoint is an isomorphism if
and only if `Hom(S, Ri_! Λ_Z) ⟶ Hom(S, L)`, `f ↦ f ≫ χ`, is bijective for every `S` supported
on `Z` (`AlgebraicGeometry.Etale.isIso_iff_isSupportedUniversal`). The forget-supports morphism
of `α ∪ β` is, up to an isomorphism of the source, the tensor product `χ_α ⊗ χ_β`, and the
universal property of `χ_α ⊗ χ_β` follows from those of `χ_α` and of the restriction of `χ_β`
to `Z₁`, using that `- ⊗ L₂` is an equivalence and the projection formula for `i₁`. In this way
no compatibility between the base change and projection isomorphisms is needed: only their
naturality.

## Main definitions

- `AlgebraicGeometry.Etale.IsSupported`: an object supported on a closed subscheme.
- `AlgebraicGeometry.Etale.IsSupportedUniversal`: the universal property of a forget-supports
  morphism.

## Main statements

- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_supportedRestrictionMap`
- `AlgebraicGeometry.Etale.isIso_iff_isSupportedUniversal`
- `AlgebraicGeometry.Etale.isIso_supportedTranspose_cupWithSupports`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Yoneda

variable {C : Type*} [Category C]

/-- A morphism precomposition with which is bijective onto every `Hom(-, T)` is an
isomorphism. -/
lemma isIso_of_bijective_comp_left {P Q : C} (w : P ⟶ Q)
    (h : ∀ T, Function.Bijective (fun f : Q ⟶ T ↦ w ≫ f)) : IsIso w := by
  obtain ⟨r, hr⟩ := (h P).2 (𝟙 P)
  dsimp only at hr
  refine ⟨r, hr, (h Q).1 ?_⟩
  dsimp only
  rw [← Category.assoc, hr, Category.id_comp, Category.comp_id]

/-- A morphism `w : P ⟶ Q` such that postcomposition with `w` is surjective from `Hom(Q, P)`
and injective on `Hom(P, P)` is an isomorphism. -/
lemma isIso_of_bijective_comp_right {P Q : C} (w : P ⟶ Q)
    (hQ : Function.Surjective (fun f : Q ⟶ P ↦ f ≫ w))
    (hP : Function.Injective (fun f : P ⟶ P ↦ f ≫ w)) : IsIso w := by
  obtain ⟨r, hr⟩ := hQ (𝟙 Q)
  dsimp only at hr
  refine ⟨r, hP ?_, hr⟩
  dsimp only
  rw [Category.assoc, hr, Category.comp_id, Category.id_comp]

/-- Postcomposition with `w ≫ w'` is bijective if postcomposition with `w` and with `w'` are. -/
lemma bijective_comp_comp {S P Q R : C} {w : P ⟶ Q} {w' : Q ⟶ R}
    (h : Function.Bijective (fun f : S ⟶ P ↦ f ≫ w))
    (h' : Function.Bijective (fun f : S ⟶ Q ↦ f ≫ w')) :
    Function.Bijective (fun f : S ⟶ P ↦ f ≫ w ≫ w') := by
  have : (fun f : S ⟶ P ↦ f ≫ w ≫ w') = (fun f ↦ f ≫ w') ∘ (fun f ↦ f ≫ w) := by
    funext f
    simp
  rw [this]
  exact h'.comp h

/-- Postcomposition with `w` is bijective if postcomposition with `w ≫ w'` and with `w'` are. -/
lemma bijective_comp_of_bijective_comp_comp {S P Q R : C} {w : P ⟶ Q} {w' : Q ⟶ R}
    (h : Function.Bijective (fun f : S ⟶ P ↦ f ≫ w ≫ w'))
    (h' : Function.Bijective (fun f : S ⟶ Q ↦ f ≫ w')) :
    Function.Bijective (fun f : S ⟶ P ↦ f ≫ w) := by
  have : (fun f : S ⟶ P ↦ f ≫ w) =
      (Equiv.ofBijective _ h').symm ∘ (fun f : S ⟶ P ↦ f ≫ w ≫ w') := by
    funext f
    apply (Equiv.ofBijective _ h').injective
    simp
  rw [this]
  exact (Equiv.ofBijective _ h').symm.bijective.comp h

/-- Postcomposition with `w` is bijective on `Hom(S, -)` if it is on `Hom(S', -)` for some
`S ≅ S'`. -/
lemma bijective_comp_of_iso_left {S S' P Q : C} (e : S ≅ S') (w : P ⟶ Q)
    (h : Function.Bijective (fun f : S' ⟶ P ↦ f ≫ w)) :
    Function.Bijective (fun f : S ⟶ P ↦ f ≫ w) := by
  have : (fun f : S ⟶ P ↦ f ≫ w) =
      (fun f ↦ e.hom ≫ f) ∘ (fun f : S' ⟶ P ↦ f ≫ w) ∘ (fun f ↦ e.inv ≫ f) := by
    funext f
    simp
  rw [this]
  exact (bijective_comp_left_of_isIso e.hom).comp (h.comp (bijective_comp_left_of_isIso e.inv))

end Yoneda

section Monoidal

/-- If `L` has a two-sided tensor inverse `L'`, then `f ↦ f ≫ χ ▷ L` is bijective on
`Hom(S, E ⊗ L)` as soon as `f ↦ f ≫ χ` is bijective on `Hom(S ⊗ L', E)`: tensoring with `L` is
an equivalence. -/
lemma bijective_comp_whiskerRight {C : Type*} [Category C] [MonoidalCategory C] {L L' : C}
    (e : L ⊗ L' ≅ 𝟙_ C) (e' : L' ⊗ L ≅ 𝟙_ C) {S E F : C} (χ : E ⟶ F)
    (h : Function.Bijective (fun f : S ⊗ L' ⟶ E ↦ f ≫ χ)) :
    Function.Bijective (fun f : S ⟶ E ⊗ L ↦ f ≫ χ ▷ L) := by
  let Eq := tensorRightEquivalenceOfTensorIso e e'
  have hF := Eq.fullyFaithfulFunctor
  have key : Function.Bijective
      (fun f : Eq.functor.obj (Eq.inverse.obj S) ⟶ Eq.functor.obj E ↦ f ≫ Eq.functor.map χ) := by
    have : (fun f : Eq.functor.obj (Eq.inverse.obj S) ⟶ Eq.functor.obj E ↦
        f ≫ Eq.functor.map χ) =
        (fun f ↦ Eq.functor.map f) ∘ (fun f : S ⊗ L' ⟶ E ↦ f ≫ χ) ∘ hF.preimage := by
      funext f
      simp only [Function.comp_apply, Functor.map_comp, Functor.FullyFaithful.map_preimage]
    rw [this]
    exact hF.map_bijective _ _ |>.comp (h.comp hF.homEquiv.symm.bijective)
  exact bijective_comp_of_iso_left (Eq.counitIso.app S).symm _ key

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- `AlgebraicGeometry.Etale.bijective_comp_whiskerRight` for the derived tensor product of
`D(X_ét)`, stated with `AlgebraicGeometry.Etale.derivedTensor`. -/
lemma bijective_comp_derivedTensor_map_app {X : Scheme.{u}}
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (e : ((derivedTensor A X).obj L).obj L' ≅ 𝟙_ _)
    (e' : ((derivedTensor A X).obj L').obj L ≅ 𝟙_ _)
    {S E F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (χ : E ⟶ F)
    (h : Function.Bijective (fun f : ((derivedTensor A X).obj S).obj L' ⟶ E ↦ f ≫ χ)) :
    Function.Bijective
      (fun f : S ⟶ ((derivedTensor A X).obj E).obj L ↦ f ≫ ((derivedTensor A X).map χ).app L) :=
  bijective_comp_whiskerRight e e' χ h

end Monoidal

variable (Λ : Type (u + 1)) [CommRing Λ]

section Support

variable {U Z Z₁ : Scheme.{u}}

/-- An object `K` of `D(U_ét)` is *supported on* the closed immersion `i : Z ⟶ U` if its
restriction to the open complement of `Z` vanishes. -/
def IsSupported (i : Z ⟶ U) [IsClosedImmersion i]
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj K)

variable {Λ}

/-- An object supported on `Z` restricts to zero on every scheme over `U` missing `Z`. -/
lemma IsSupported.isZero_leftDerivedUpperStar {i : Z ⟶ U} [IsClosedImmersion i]
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsSupported Λ i K) {V : Scheme.{u}} (v : V ⟶ U)
    (hv : Disjoint (Set.range v.base) (Set.range i.base)) :
    IsZero ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  set j := i.openComplement.ι
  have hv' : Set.range v.base ⊆ Set.range j.base := by
    rw [← compl_compl (Set.range j.base), ← i.range_eq_compl_range_openComplement_ι]
    exact hv.subset_compl_right
  rw [← IsOpenImmersion.lift_fac j v hv']
  exact ((L((IsOpenImmersion.lift j v hv')^*[ModuleCat.{u + 1} Λ])).map_isZero hK).of_iso
    ((leftDerivedUpperStarComp _ _ j).app _)

/-- The range of the open complement of a closed immersion is disjoint from its range. -/
lemma disjoint_range_openComplement_ι (i : Z ⟶ U) [IsClosedImmersion i] :
    Disjoint (Set.range i.openComplement.ι.base) (Set.range i.base) := by
  rw [i.range_eq_compl_range_openComplement_ι]
  exact disjoint_compl_right

/-- An object supported on `Z` is supported on every closed subscheme containing `Z`. -/
lemma IsSupported.mono {i : Z ⟶ U} {i₁ : Z₁ ⟶ U} [IsClosedImmersion i] [IsClosedImmersion i₁]
    (h : Set.range i.base ⊆ Set.range i₁.base)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsSupported Λ i K) : IsSupported Λ i₁ K :=
  hK.isZero_leftDerivedUpperStar _ ((disjoint_range_openComplement_ι i₁).mono_right h)

/-- A tensor product with an object supported on `Z` is supported on `Z`. -/
lemma IsSupported.derivedTensor {i : Z ⟶ U} [IsClosedImmersion i]
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsSupported Λ i K)
    (M : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsSupported Λ i (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj M) :=
  (isZero_derivedTensor_obj_obj_of_isZero_left hK _).of_iso (leftDerivedUpperStarTensorIso _ _ _ _)

/-- The pullback of an object supported on `Z` along `e : U' ⟶ U` is supported on every closed
`Z' ⊆ U'` whose complement maps into the complement of `Z`. -/
lemma IsSupported.leftDerivedUpperStar {U' Z' : Scheme.{u}} {i : Z ⟶ U} {i' : Z' ⟶ U'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (e : U' ⟶ U)
    (he : Disjoint (Set.range (i'.openComplement.ι ≫ e).base) (Set.range i.base))
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsSupported Λ i K) :
    IsSupported Λ i' ((L((e)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (hK.isZero_leftDerivedUpperStar _ he).of_iso
    ((leftDerivedUpperStarComp _ i'.openComplement.ι e).app K).symm

variable (Λ) in
/-- An object `Ri_! B` is supported on `Z`. -/
lemma isSupported_rightDerivedLowerShriek (i : Z ⟶ U) [IsClosedImmersion i]
    (B : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsSupported Λ i ((R(i)_![ModuleCat.{u + 1} Λ]).obj B) :=
  isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i B _
    (disjoint_range_openComplement_ι i)

end Support

section Reflection

variable {U Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]

/-- For a closed immersion `i` and `w : K ⟶ T`, precomposition with `w` is bijective onto
`Hom(-, Ri_! N)` for every `N` if and only if `Li^* w` is an isomorphism: by `Ri_! ≅ Ri_*` and
the adjunction `Li^* ⊣ Ri_*`, it is precomposition with `Li^* w` onto `Hom(-, N)`. -/
lemma bijective_comp_rightDerivedLowerShriek_iff
    {K T : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (w : K ⟶ T) :
    (∀ N, Function.Bijective
        (fun f : T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N ↦ w ≫ f)) ↔
      IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map w) := by
  let θ := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  let E : ∀ X N, (X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N) ≃
      ((L((i)^*[ModuleCat.{u + 1} Λ])).obj X ⟶ N) := fun X N ↦
    ((Iso.refl X).homCongr (θ.app N)).trans (adj.homEquiv X N).symm
  have hE : ∀ N (f : T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N),
      E K N (w ≫ f) = (L((i)^*[ModuleCat.{u + 1} Λ])).map w ≫ E T N f := by
    intro N f
    simp only [E, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Category.assoc, Adjunction.homEquiv_naturality_left_symm]
  constructor
  · intro h
    refine isIso_of_bijective_comp_left _ fun N ↦ ?_
    have : (fun g ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map w ≫ g) =
        E K N ∘ (fun f : T ⟶ _ ↦ w ≫ f) ∘ (E T N).symm := by
      funext g
      simp [hE]
    rw [this]
    exact (E K N).bijective.comp ((h N).comp (E T N).symm.bijective)
  · intro h N
    have : (fun f : T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N ↦ w ≫ f) =
        (E K N).symm ∘ (fun g ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map w ≫ g) ∘ E T N := by
      funext f
      simp only [Function.comp_apply]
      rw [← hE, Equiv.symm_apply_apply]
    rw [this]
    exact (E K N).symm.bijective.comp ((bijective_comp_left_of_isIso _).comp (E T N).bijective)

/-- The pullback `Li^* u` of the restriction map `u : Λ_U ⟶ Ri_! Λ_Z` is an isomorphism. -/
lemma isIso_leftDerivedUpperStar_map_supportedRestrictionMap :
    IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ i)) :=
  (bijective_comp_rightDerivedLowerShriek_iff Λ i _).1 (bijective_supportedRestrictionMap_comp Λ i)

/-- **Reflections agree.** Two morphisms `w₁ : K ⟶ T₁`, `w₂ : K ⟶ T₂` into objects supported on
`Z` which become isomorphisms after `Li^*` differ by a unique isomorphism `T₁ ≅ T₂`. -/
lemma exists_iso_comp_eq
    {K T₁ T₂ : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h₁ : IsSupported Λ i T₁) (h₂ : IsSupported Λ i T₂) (w₁ : K ⟶ T₁) (w₂ : K ⟶ T₂)
    (hw₁ : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map w₁))
    (hw₂ : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map w₂)) :
    ∃ a : T₁ ≅ T₂, w₁ ≫ a.hom = w₂ := by
  have := isIso_counit_app_of_isZero Λ i T₁ h₁
  have := isIso_counit_app_of_isZero Λ i T₂ h₂
  let θ₁ := (asIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app
    T₁)).symm
  let θ₂ := (asIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app
    T₂)).symm
  have b₁₁ := bijective_comp_of_iso w₁ θ₁
    ((bijective_comp_rightDerivedLowerShriek_iff Λ i w₁).2 hw₁ _)
  have b₁₂ := bijective_comp_of_iso w₁ θ₂
    ((bijective_comp_rightDerivedLowerShriek_iff Λ i w₁).2 hw₁ _)
  have b₂₁ := bijective_comp_of_iso w₂ θ₁
    ((bijective_comp_rightDerivedLowerShriek_iff Λ i w₂).2 hw₂ _)
  have b₂₂ := bijective_comp_of_iso w₂ θ₂
    ((bijective_comp_rightDerivedLowerShriek_iff Λ i w₂).2 hw₂ _)
  obtain ⟨a, ha⟩ := b₁₂.2 w₂
  obtain ⟨b, hb⟩ := b₂₁.2 w₁
  dsimp only at ha hb
  have hab : a ≫ b = 𝟙 _ := b₁₁.1 (by dsimp only; rw [← Category.assoc, ha, hb, Category.comp_id])
  have hba : b ≫ a = 𝟙 _ := b₂₂.1 (by dsimp only; rw [← Category.assoc, hb, ha, Category.comp_id])
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

end Reflection

section Universal

variable {U Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]

/-- A morphism `χ : E ⟶ L` is *universal for objects supported on `Z`* if `f ↦ f ≫ χ` is a
bijection `Hom(S, E) ≅ Hom(S, L)` for every `S` supported on `Z`. For the counit
`Ri_! Ri^! L ⟶ L` this is the universal property of `Ri^!`; for the forget-supports morphism
`Ri_! Λ_Z ⟶ L` of a class with supports it says that the class is a Thom class
(`AlgebraicGeometry.Etale.isIso_iff_isSupportedUniversal`). -/
def IsSupportedUniversal
    {E L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (χ : E ⟶ L) : Prop :=
  ∀ S, IsSupported Λ i S → Function.Bijective (fun f : S ⟶ E ↦ f ≫ χ)

/-- The counit `Ri_! Ri^! L ⟶ L` is universal for objects supported on `Z`. -/
lemma bijective_comp_counit
    {S : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : IsSupported Λ i S)
    (L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun f : S ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj L) ↦
      f ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L) := by
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨_, _, h⟩ := existsUnique_comp_counit_of_isZero _ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι hS
      (f ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L)
    exact (h f rfl).trans (h g hfg.symm).symm
  · obtain ⟨ψ, hψ, _⟩ := existsUnique_comp_counit_of_isZero _ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι hS φ
    exact ⟨ψ, hψ⟩

/-- **Thom classes by a universal property.** A morphism `φ : N ⟶ Ri^! L` is an isomorphism
if and only if its transpose `Ri_! N ⟶ Ri_! Ri^! L ⟶ L` is universal for objects supported on
`Z`. -/
lemma isIso_iff_isSupportedUniversal
    {N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : N ⟶ (R(i)^![ModuleCat.{u + 1} Λ]).obj L) :
    IsIso φ ↔ IsSupportedUniversal Λ i ((R(i)_![ModuleCat.{u + 1} Λ]).map φ ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app L) := by
  constructor
  · intro hφ S hS
    exact bijective_comp_comp (bijective_comp_right_of_isIso _) (bijective_comp_counit Λ i hS L)
  · intro h
    have hb : ∀ S, IsSupported Λ i S → Function.Bijective
        (fun f : S ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N ↦
          f ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map φ) := fun S hS ↦
      bijective_comp_of_bijective_comp_comp (h S hS) (bijective_comp_counit Λ i hS L)
    have : IsIso ((R(i)_![ModuleCat.{u + 1} Λ]).map φ) :=
      isIso_of_bijective_comp_right _
        (hb _ (isSupported_rightDerivedLowerShriek Λ i _)).2
        (hb _ (isSupported_rightDerivedLowerShriek Λ i _)).1
    exact isIso_of_reflects_iso φ (R(i)_![ModuleCat.{u + 1} Λ])

end Universal

section Restriction

variable {U U' Z₂ Z' : Scheme.{u}} (e : U' ⟶ U) (i₂ : Z₂ ⟶ U) (b : Z' ⟶ U')
  [IsClosedImmersion i₂] [IsClosedImmersion b] (g : Z' ⟶ Z₂) (hg : IsPullback g b i₂ e)

/-- **Forget supports after restriction.** Let `β` be a class supported on `Z₂` and `β'` its
restriction along `e : U' ⟶ U` to the base change `b : Z' ⟶ U'`. Up to an isomorphism
`Rb_! Λ_{Z'} ≅ Le^* Ri₂_! Λ_{Z₂}` of the sources, the forget-supports morphism of `β'` is the
pullback of that of `β`, followed by `τ`. -/
lemma exists_iso_forget_restrictSupportedClass
    {L₂ : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L₂' : _root_.DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L₂ ≅ L₂')
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![ModuleCat.{u + 1} Λ]).obj L₂)) :
    ∃ σ : (R(b)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z') ≅
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)),
      (R(b)_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ b
          (restrictSupportedClass (ModuleCat.{u + 1} Λ) e i₂ b g hg
            (leftDerivedUpperStarConstantComplexIso Λ e).inv τ β)) ≫
          (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) b).counit.app L₂' =
        σ.hom ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map
          ((R(i₂)_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i₂ β) ≫
            (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₂).counit.app L₂) ≫
          τ.hom := by
  set A := ModuleCat.{u + 1} Λ
  set u₂ := supportedRestrictionMap Λ i₂
  set v := (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫ (L((e)^*[A])).map u₂
  have hsupp : IsSupported Λ b ((L((e)^*[A])).obj ((R(i₂)_![A]).obj (constantComplex Λ Z₂))) :=
    isZero_leftDerivedUpperStar_openComplement_obj Λ e i₂ b g hg _
  have hub := isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ b
  have hv : IsIso ((L((b)^*[A])).map v) := by
    have := isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ i₂
    have h₂ : IsIso ((L((i₂)^*[A]) ⋙ L((g)^*[A])).map u₂) :=
      inferInstanceAs (IsIso ((L((g)^*[A])).map ((L((i₂)^*[A])).map u₂)))
    have h₁ : IsIso ((L((e)^*[A]) ⋙ L((b)^*[A])).map u₂) :=
      (NatIso.isIso_map_iff ((leftDerivedUpperStarComp A b e (g ≫ i₂) hg.w).symm ≪≫
        leftDerivedUpperStarComp A g i₂) u₂).2 h₂
    have : IsIso ((L((b)^*[A])).map ((L((e)^*[A])).map u₂)) := h₁
    simp only [v, Functor.map_comp]
    infer_instance
  obtain ⟨σ, hσ⟩ := exists_iso_comp_eq Λ b (isSupported_rightDerivedLowerShriek Λ b _) hsupp
    (supportedRestrictionMap Λ b) v hub hv
  refine ⟨σ, ?_⟩
  have hψ : supportedRestriction A e i₂ b g hg L₂ L₂' τ ≫
      (rightDerivedUpperShriekAdjunction A b).counit.app L₂' =
        (L((e)^*[A])).map ((rightDerivedUpperShriekAdjunction A i₂).counit.app L₂) ≫ τ.hom :=
    (existsUnique_supportedRestriction A e i₂ b g hg L₂ L₂' τ).exists.choose_spec
  have hβ' : u₂ ≫ (R(i₂)_![A]).map (supportedTranspose Λ i₂ β) = β :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i₂ β
  have key : (R(b)_![A]).map (supportedTranspose Λ b
      (restrictSupportedClass A e i₂ b g hg (leftDerivedUpperStarConstantComplexIso Λ e).inv τ
        β)) =
      σ.hom ≫ (L((e)^*[A])).map ((R(i₂)_![A]).map (supportedTranspose Λ i₂ β)) ≫
        supportedRestriction A e i₂ b g hg L₂ L₂' τ := by
    apply (bijective_supportedRestrictionMap_comp Λ b _).1
    dsimp only
    rw [supportedRestrictionMap_comp_map_supportedTranspose, ← Category.assoc, hσ]
    simp only [v, restrictSupportedClass, Category.assoc, ← Functor.map_comp_assoc, hβ']
  rw [key, Category.assoc, Category.assoc]
  erw [hψ]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end Restriction

section Product

variable [Finite Λ] {U Z₁ Z₂ Z : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]

set_option maxHeartbeats 1000000 in
-- the kernel rechecks the defeqs of the transport along the projection formula
/-- **The cup product of Thom classes.** Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` be closed immersions
meeting in `i : Z ⟶ U` (with `Z ⊆ Z₁` and `Z ⊆ Z₂` scheme-theoretically), `b : Z' ⟶ Z₁` the
base change of `i₂` along `i₁`, and let `α ∈ H_{Z₁}(U, L₁)`, `β ∈ H_{Z₂}(U, L₂)` be classes with
supports, `L₂` invertible. If the adjoint of `α` is an isomorphism and the adjoint of the
restriction of `β` to `Z₁` is an isomorphism, then the adjoint `Λ_Z ⟶ Ri^! (L₁ ⊗ L₂)` of the
cup product with supports `α ∪ β` is an isomorphism. -/
theorem isIso_supportedTranspose_cupWithSupports
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (b₁ : Z ⟶ Z₁) (hb₁ : b₁ ≫ i₁ = i) (b₂ : Z ⟶ Z₂) (hb₂ : b₂ ≫ i₂ = i)
    {Z' : Scheme.{u}} (b : Z' ⟶ Z₁) [IsClosedImmersion b] (g : Z' ⟶ Z₂)
    (hg : IsPullback g b i₂ i₁)
    {L₁ L₂ : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL₂ : DerivedCategory.isInvertible Λ U L₂)
    {L₂' : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj L₂ ≅ L₂')
    (Δ : constantComplex Λ U ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      (constantComplex Λ U)).obj (constantComplex Λ U)) [IsIso Δ]
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![ModuleCat.{u + 1} Λ]).obj L₁))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![ModuleCat.{u + 1} Λ]).obj L₂))
    (hα : IsIso (supportedTranspose Λ i₁ α))
    (hβ : IsIso (supportedTranspose Λ b (restrictSupportedClass (ModuleCat.{u + 1} Λ) i₁ i₂ b g
      hg (leftDerivedUpperStarConstantComplexIso Λ i₁).inv τ β))) :
    IsIso (supportedTranspose Λ i (cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β)) := by
  set u₁ := supportedRestrictionMap Λ i₁
  set u₂ := supportedRestrictionMap Λ i₂
  set φ₁ := supportedTranspose Λ i₁ α
  set φ₂ := supportedTranspose Λ i₂ β
  set χ₁ := (R(i₁)_![ModuleCat.{u + 1} Λ]).map φ₁ ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₁).counit.app L₁
  set χ₂ := (R(i₂)_![ModuleCat.{u + 1} Λ]).map φ₂ ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₂).counit.app L₂
  set Q := derivedTensorHom (ModuleCat.{u + 1} Λ) ((R(i₁)_![ModuleCat.{u + 1} Λ]).map φ₁)
      ((R(i₂)_![ModuleCat.{u + 1} Λ]).map φ₂) ≫
    supportedProduct (ModuleCat.{u + 1} Λ) i₁ i₂ i h L₁ L₂
  set w := Δ ≫ derivedTensorHom (ModuleCat.{u + 1} Λ) u₁ u₂
  have hα' : u₁ ≫ (R(i₁)_![ModuleCat.{u + 1} Λ]).map φ₁ = α :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i₁ α
  have hβ' : u₂ ≫ (R(i₂)_![ModuleCat.{u + 1} Λ]).map φ₂ = β :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i₂ β
  have hcup : cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β = w ≫ Q := by
    rw [cupWithSupports_eq, ← hα', ← hβ', ← derivedTensorHom_comp]
    simp only [w, Q, Category.assoc]
  have hsub₁ : Set.range i.base ⊆ Set.range i₁.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨b₁.base z, by rw [← Scheme.Hom.comp_apply, hb₁]⟩
  -- the source `E₁ ⊗ E₂` of `Q` is supported on `Z`
  have hT : IsSupported Λ i (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
        ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂))) :=
    isZero_leftDerivedUpperStar_derivedTensor_of_disjoint _ i₁ i₂ i h
      (fun v hv ↦ isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i₁ _ v hv)
      (fun v hv ↦ isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i₂ _ v hv)
      _ (disjoint_range_openComplement_ι i)
  -- `Λ_U ⟶ Ri_! Λ_Z` and `Λ_U ⟶ E₁ ⊗ E₂` are reflections, so they differ by an isomorphism
  have hLw : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map w) := by
    have hu : ∀ {Y : Scheme.{u}} (c : Y ⟶ U) [IsClosedImmersion c] (d : Z ⟶ Y),
        d ≫ c = i → IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ c)) := by
      intro Y c _ d hd
      have := isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ c
      have : IsIso ((L((c)^*[ModuleCat.{u + 1} Λ]) ⋙ L((d)^*[ModuleCat.{u + 1} Λ])).map
          (supportedRestrictionMap Λ c)) :=
        inferInstanceAs (IsIso ((L((d)^*[ModuleCat.{u + 1} Λ])).map
          ((L((c)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ c))))
      exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp _ d c i hd.symm) _).2 this
    have hu₁ := hu i₁ b₁ hb₁
    have hu₂ := hu i₂ b₂ hb₂
    have : IsIso (derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((L((i)^*[ModuleCat.{u + 1} Λ])).map u₁) ((L((i)^*[ModuleCat.{u + 1} Λ])).map u₂)) := by
      unfold derivedTensorHom
      infer_instance
    have hn := leftDerivedUpperStarTensorIso_hom_naturality (ModuleCat.{u + 1} Λ) i u₁ u₂
    have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorHom (ModuleCat.{u + 1} Λ) u₁ u₂) ≫
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) i _ _).hom) := by
      rw [hn]
      infer_instance
    have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorHom (ModuleCat.{u + 1} Λ) u₁ u₂)) :=
      IsIso.of_isIso_comp_right _ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) i _ _).hom
    simp only [w, Functor.map_comp]
    infer_instance
  obtain ⟨a, ha⟩ := exists_iso_comp_eq Λ i (isSupported_rightDerivedLowerShriek Λ i _) hT
    (supportedRestrictionMap Λ i) w (isIso_leftDerivedUpperStar_map_supportedRestrictionMap Λ i)
    hLw
  -- `Ri_! ψ = a ≫ Q`
  have hψ : (R(i)_![ModuleCat.{u + 1} Λ]).map
      (supportedTranspose Λ i (cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β)) =
        a.hom ≫ Q := by
    apply (bijective_supportedRestrictionMap_comp Λ i _).1
    dsimp only
    rw [supportedRestrictionMap_comp_map_supportedTranspose, ← Category.assoc, ha, hcup]
  suffices hQ : IsIso Q by
    have : IsIso ((R(i)_![ModuleCat.{u + 1} Λ]).map
        (supportedTranspose Λ i (cupWithSupports (ModuleCat.{u + 1} Λ) i₁ i₂ i h Δ α β))) := by
      rw [hψ]
      infer_instance
    exact isIso_of_reflects_iso _ (R(i)_![ModuleCat.{u + 1} Λ])
  -- the composite of `Q` with the counit is `χ₁ ⊗ χ₂`
  have hQε : Q ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app
      (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj L₁).obj L₂) =
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).map χ₂ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).map χ₁).app L₂ := by
    have : Q ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj L₁).obj L₂) =
        derivedTensorHom (ModuleCat.{u + 1} Λ) χ₁ χ₂ := by
      simp only [Q, χ₁, χ₂, Category.assoc, supportedProduct_comp_counit, derivedTensorHom_comp]
    rw [this]
    exact (((derivedTensor (ModuleCat.{u + 1} Λ) U).map χ₁).naturality χ₂).symm
  -- `- ⊗ L₂` and the universal property of `χ₁`
  have h₁ : ∀ S, IsSupported Λ i S → Function.Bijective
      (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj L₂ ↦
          f ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).map χ₁).app L₂) := by
    obtain ⟨M, ⟨eM⟩, ⟨eM'⟩⟩ := hL₂
    have huniv₁ := (isIso_iff_isSupportedUniversal Λ i₁ φ₁).1 hα
    intro S hS
    exact bijective_comp_derivedTensor_map_app _ eM eM' χ₁
      (huniv₁ _ ((hS.derivedTensor M).mono hsub₁))
  -- the projection formula for `i₁` and the universal property of the restriction of `χ₂`
  have h₂ : ∀ S, IsSupported Λ i S → Function.Bijective
      (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
        f ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).map χ₂) := by
    intro S hS
    obtain ⟨σ, hσ⟩ := exists_iso_forget_restrictSupportedClass Λ i₁ i₂ b g hg τ β
    have huniv₂ := (isIso_iff_isSupportedUniversal Λ b _).1 hβ
    -- `L i₁^* S` is supported on `Z'`
    have hS' : IsSupported Λ b ((L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S) := by
      refine hS.leftDerivedUpperStar i₁ ?_
      rw [Set.disjoint_left]
      rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
      apply y.2
      rw [Scheme.range_snd_of_isPullback hg]
      refine ⟨b₂.base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hb₂, hz, Scheme.Hom.comp_apply]
      rfl
    have hχ₂ : Function.Bijective
        (fun f : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S ⟶ (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
          f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂) := by
      have h0 := huniv₂ _ hS'
      simp only [hσ] at h0
      have : (fun f : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S ⟶
            (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
              ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
            f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂) =
          (fun f ↦ f ≫ τ.inv) ∘
            (fun f ↦ f ≫ σ.hom ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂ ≫ τ.hom) ∘
              (fun f ↦ f ≫ σ.inv) := by
        funext f
        simp
      rw [this]
      exact (bijective_comp_right_of_isIso _).comp (h0.comp (bijective_comp_right_of_isIso _))
    -- transport along the projection formula and the adjunction `Li₁^* ⊣ Ri₁_*`
    have := isIso_projectionMap_of_finite Λ i₁
    let PF := (projectionMap (ModuleCat.{u + 1} Λ) i₁).app (constantComplex Λ Z₁)
    let θ := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i₁
    let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i₁
    let lZ := derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) Z₁
    -- the isomorphism `ν : E₁ ⊗ X ≅ Ri₁_* Li₁^* X`, natural in `X`
    let ν : (derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁)) ⟶
          L((i₁)^*[ModuleCat.{u + 1} Λ]) ⋙ R((i₁)_*[ModuleCat.{u + 1} Λ]) :=
      PF ≫ Functor.whiskerLeft L((i₁)^*[ModuleCat.{u + 1} Λ])
          (Functor.whiskerRight lZ.hom R(i₁)_![ModuleCat.{u + 1} Λ]) ≫
        Functor.whiskerLeft L((i₁)^*[ModuleCat.{u + 1} Λ]) θ.hom
    have hνi : ∀ X, IsIso (ν.app X) := fun X ↦ by
      dsimp only [ν, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance
    let Φ : ∀ X, (S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj X) ≃
        ((L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S ⟶ (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj X) :=
      fun X ↦
        { toFun := fun f ↦ (adj.homEquiv _ _).symm (f ≫ ν.app X)
          invFun := fun g ↦ adj.homEquiv _ _ g ≫ inv (ν.app X)
          left_inv := fun f ↦ by simp
          right_inv := fun g ↦ by simp }
    have hΦ : ∀ (f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
          ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂))),
        Φ L₂ (f ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).map χ₂) =
          Φ _ f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂ := by
      intro f
      change (adj.homEquiv _ _).symm ((f ≫ _) ≫ ν.app L₂) =
        (adj.homEquiv _ _).symm (f ≫ ν.app _) ≫ _
      rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc]
      erw [ν.naturality χ₂]
      rw [Category.assoc]
      rfl
    have : (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦
          f ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
            ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).map χ₂) =
        (Φ L₂).symm ∘ (fun f ↦ f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map χ₂) ∘ Φ _ := by
      funext f
      simp only [Function.comp_apply]
      rw [← hΦ, Equiv.symm_apply_apply]
    rw [this]
    exact (Φ L₂).symm.bijective.comp (hχ₂.comp (Φ _).bijective)
  have hbQ : ∀ S, IsSupported Λ i S → Function.Bijective
      (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₁))).obj
            ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z₂)) ↦ f ≫ Q) :=
    fun S hS ↦ by
      have h := bijective_comp_comp (h₂ S hS) (h₁ S hS)
      rw [← hQε] at h
      exact bijective_comp_of_bijective_comp_comp h (bijective_comp_counit Λ i hS _)
  exact isIso_of_bijective_comp_right _ (hbQ _ (isSupported_rightDerivedLowerShriek Λ i _)).2
    (hbQ _ hT).1

end Product

end Etale

end AlgebraicGeometry
