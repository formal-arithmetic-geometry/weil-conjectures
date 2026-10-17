/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedExteriorProduct
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.Etale.Derived.Composition

/-!
# Künneth with supports

For closed subschemes `Z ⊆ X`, `W ⊆ Y` of schemes of finite type over a separably closed field,
the supported exterior product
`RΓ_Z(X, K) ⊗ᴸ RΓ_W(Y, L) ⟶ RΓ_{Z × W}(X × Y, K ⊠ L)`
(`AlgebraicGeometry.Etale.supportedExteriorProduct`) is an isomorphism
(`lem-pur-kunneth-supported`).

The supported exterior product is the Künneth map, an isomorphism, followed by `Rc_*` of the
product of supports `Φ : Ri₁_! Ri₁^! p^*K ⊗ Rj₁_! Rj₁^! q^*L ⟶ Rι_! Rι^!(K ⊠ L)`. We show that `Φ`
itself is an isomorphism. Its source is supported on `Z × W`, and its composite with the counit
is `ε_K ⊠ ε_L`, so it suffices that `Rι^!(ε_K ⊠ ε_L)` is an isomorphism. Factor `ε_K ⊠ ε_L`
through `K ⊠ (Rj_! Rj^! L)`: the cones are `(Rj_U* K|_U) ⊠ Rj_! Rj^! L` and `K ⊠ (Rj_V* L|_V)`,
where `U`, `V` are the complements of `Z`, `W`, and these are pushed forward from `U × Y` and
`X × V` by the base change theorem for a pushforward tensored with a complex
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`, `lem-kun-0f1n`), so `Rι^!` kills them.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y P : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ aX aY)

section Vanishing

/-- The second leg of a pullback square has range the preimage of the range of the opposite
leg. -/
lemma _root_.AlgebraicGeometry.Scheme.range_snd_of_isPullback' {Q A B C : Scheme.{u}}
    {fst : Q ⟶ A} {snd : Q ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  have hsurj : Function.Surjective ⇑h.isoPullback.hom := by
    have := (Scheme.homeoOfIso h.isoPullback).surjective
    rwa [Scheme.coe_homeoOfIso] at this
  rw [← h.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_snd]

include hP in
/-- `Rw₁^!(p₁^* E ⊗ p₂^* Rj_* F) = 0` for an open immersion `j : V ⟶ Y` with closed complement
`w : W ⟶ Y`, `w₁` the preimage of `w` in `X × Y`: by the base change theorem, the tensor product
is pushed forward from the preimage `X × V` of `V`. -/
theorem isZero_rightDerivedUpperShriek_derivedTensor_lowerStar
    {W V W₁ P' : Scheme.{u}} (w : W ⟶ Y) [IsClosedImmersion w] (j : V ⟶ Y) [IsOpenImmersion j]
    [QuasiCompact j] (hwj : Set.range w.base = (Set.range j.base)ᶜ)
    (w₁ : W₁ ⟶ P) [IsClosedImmersion w₁] (gw : W₁ ⟶ W) (hw : IsPullback gw w₁ w p₂)
    (h : P' ⟶ P) (e : P' ⟶ V) (sq : IsPullback h e p₂ j)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((R(w₁)^![ModuleCat.{u + 1} Λ]).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
        ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj F)))) := by
  have : IsOpenImmersion h := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have hiso := isIso_tensorBaseChangeMap Λ aX aY (j ≫ aY) p₁ p₂ h e j rfl hP sq E F
  have hcompl : Set.range w₁.base = (Set.range h.base)ᶜ := by
    change Set.range w₁ = (Set.range h)ᶜ
    rw [Scheme.range_snd_of_isPullback' hw, Scheme.range_snd_of_isPullback' sq.flip, hwj]
    rfl
  exact (isZero_rightDerivedUpperShriek_obj_rightDerivedLowerStar_obj w₁ h hcompl _).of_iso
    ((R(w₁)^![ModuleCat.{u + 1} Λ]).mapIso (asIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e
      p₂ j sq.w ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E) F)))

end Vanishing
section TensorTriangle

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X₀ : Scheme.{u}} {D : Type*} [Category D]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- For a triangulated `F`, if `F` kills `K ⊗ T₃` for a distinguished triangle `T`, then `F`
inverts `K ⊗ T.mor₁`. -/
lemma isIso_map_derivedTensor_obj_map_of_isZero
    (F : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology A) ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (K : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology A))
    {T : Triangle (_root_.DerivedCategory (Sheaf X₀.smallEtaleTopology A))}
    (hT : T ∈ distTriang _) (h : IsZero (F.obj (((derivedTensor A X₀).obj K).obj T.obj₃))) :
    IsIso (F.map (((derivedTensor A X₀).obj K).map T.mor₁)) := by
  let := _root_.DerivedCategory.commShiftTensorLeft (K := K)
  have : ((derivedTensor A X₀).obj K).IsTriangulated :=
    _root_.DerivedCategory.isTriangulated_tensorLeft (K := K)
  exact (Triangle.isZero₃_iff_isIso₁ _
    (F.map_distinguished _ (((derivedTensor A X₀).obj K).map_distinguished _ hT))).1 h

/-- For a triangulated `F`, if `F` kills `T₃ ⊗ K` for a distinguished triangle `T`, then `F`
inverts `T.mor₁ ⊗ K`. -/
lemma isIso_map_derivedTensor_map_app_of_isZero
    (F : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology A) ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (K : _root_.DerivedCategory (Sheaf X₀.smallEtaleTopology A))
    {T : Triangle (_root_.DerivedCategory (Sheaf X₀.smallEtaleTopology A))}
    (hT : T ∈ distTriang _) (h : IsZero (F.obj (((derivedTensor A X₀).obj T.obj₃).obj K))) :
    IsIso (F.map (((derivedTensor A X₀).map T.mor₁).app K)) := by
  let := _root_.DerivedCategory.commShiftTensorRight (K := K)
  have : ((derivedTensor A X₀).flip.obj K).IsTriangulated :=
    _root_.DerivedCategory.isTriangulated_tensorRight (K := K)
  exact (Triangle.isZero₃_iff_isIso₁ _
    (F.map_distinguished _ (((derivedTensor A X₀).flip.obj K).map_distinguished _ hT))).1 h

end TensorTriangle

section Local

variable {Z U W V Z₁ W₁ T PU PV : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (jU : U ⟶ X) [IsOpenImmersion jU] [QuasiCompact jU]
  (hU : Set.range i.base = (Set.range jU.base)ᶜ)
  (w : W ⟶ Y) [IsClosedImmersion w] (jV : V ⟶ Y) [IsOpenImmersion jV] [QuasiCompact jV]
  (hV : Set.range w.base = (Set.range jV.base)ᶜ)
  (i₁ : Z₁ ⟶ P) [IsClosedImmersion i₁] (gi : Z₁ ⟶ Z) (hi : IsPullback gi i₁ i p₁)
  (w₁ : W₁ ⟶ P) [IsClosedImmersion w₁] (gw : W₁ ⟶ W) (hw : IsPullback gw w₁ w p₂)
  (hU₁ : PU ⟶ P) (eU : PU ⟶ U) (sqU : IsPullback hU₁ eU p₁ jU)
  (hV₁ : PV ⟶ P) (eV : PV ⟶ V) (sqV : IsPullback hV₁ eV p₂ jV)
  (ι : T ⟶ P) [IsClosedImmersion ι] (b₁ : T ⟶ Z₁) (hb₁ : b₁ ≫ i₁ = ι)
  (b₂ : T ⟶ W₁) (hb₂ : b₂ ≫ w₁ = ι)

include hP hV hw sqV hb₂ in
/-- `Rι^!` inverts `p₁^* K ⊗ p₂^* ε_L`, `ε_L : Rw_! Rw^! L ⟶ L` the counit: its cone is
`p₁^* K ⊗ p₂^* Rj_{V*} L|_V`, killed by `Rw₁^!`. -/
theorem isIso_rightDerivedUpperShriek_map_tensor_counit_right
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R(ι)^![ModuleCat.{u + 1} Λ]).map
      (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj K)).map
        ((L((p₂)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) w).counit.app L)))) := by
  set A := ModuleCat.{u + 1} Λ
  have hT := supportedLocalizationTriangle_mem_distTriang A w jV hV L
  have hT₁ := (L((p₂)^*[A])).map_distinguished _ hT
  have := (rightDerivedUpperShriekAdjunction A ι).commShift_of_leftAdjoint ℤ
  have := isTriangulated_rightDerivedUpperShriek (Λ := Λ) ι
  refine isIso_map_derivedTensor_obj_map_of_isZero (R(ι)^![A]) _ hT₁ ?_
  -- the third object: `Rι^!(p₁^* K ⊗ p₂^* Rj_{V*} L|_V) = Rb₂^! Rw₁^!(…) = 0`
  have hz := isZero_rightDerivedUpperShriek_derivedTensor_lowerStar Λ aX aY p₁ p₂ hP w jV hV
    w₁ gw hw hV₁ eV sqV K ((L((jV)^*[A])).obj L)
  have : IsClosedImmersion (b₂ ≫ w₁) := hb₂ ▸ inferInstance
  have : IsClosedImmersion b₂ := IsClosedImmersion.of_comp b₂ w₁
  have : HasCompactification (b₂ ≫ w₁) := .of_eq hb₂.symm
  have : QuasiCompact (b₂ ≫ w₁) := by rw [hb₂]; infer_instance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ b₂ w₁
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq A hb₂.symm
  exact ((R(b₂)^![A]).map_isZero hz).of_iso (heq.app _ ≪≫ c.app _)

end Local

end AlgebraicGeometry.Etale
