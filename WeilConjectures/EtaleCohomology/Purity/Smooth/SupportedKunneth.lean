/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedExteriorProduct
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassProduct
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
  have : IsOpenImmersion h :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have hiso := isIso_tensorBaseChangeMap Λ aX aY (j ≫ aY) p₁ p₂ h e j rfl hP sq E F
  have hcompl : Set.range w₁.base = (Set.range h.base)ᶜ := by
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
  have hT := supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ) w jV hV L
  have hT₁ := (L((p₂)^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT
  have := isTriangulated_rightDerivedUpperShriek (Λ := Λ) ι
  refine isIso_map_derivedTensor_obj_map_of_isZero (A := ModuleCat.{u + 1} Λ)
    (R(ι)^![ModuleCat.{u + 1} Λ]) _ hT₁ ?_
  -- the third object: `Rι^!(p₁^* K ⊗ p₂^* Rj_{V*} L|_V) = Rb₂^! Rw₁^!(…) = 0`
  have hz := isZero_rightDerivedUpperShriek_derivedTensor_lowerStar Λ aX aY p₁ p₂ hP w jV hV
    w₁ gw hw hV₁ eV sqV K ((L((jV)^*[ModuleCat.{u + 1} Λ])).obj L)
  have : IsClosedImmersion (b₂ ≫ w₁) := hb₂ ▸ inferInstance
  have : IsClosedImmersion b₂ := IsClosedImmersion.of_comp b₂ w₁
  have : HasCompactification (b₂ ≫ w₁) := .of_eq hb₂.symm
  have : QuasiCompact (b₂ ≫ w₁) := by rw [hb₂]; infer_instance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ b₂ w₁
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) hb₂.symm
  exact ((R(b₂)^![ModuleCat.{u + 1} Λ]).map_isZero hz).of_iso (heq.app _ ≪≫ c.app _)
include hP hU hi sqU hb₁ in
/-- `Rι^!` inverts `p₁^* ε_K ⊗ M` for `M` on `X × Y` pulled back from `Y`, `ε_K : Ri_! Ri^! K ⟶ K`
the counit: its cone is `p₁^* Rj_{U*} K|_U ⊗ M`, killed by `Ri₁^!`. -/
theorem isIso_rightDerivedUpperShriek_map_counit_tensor_left
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((R(ι)^![ModuleCat.{u + 1} Λ]).map
      (((derivedTensor (ModuleCat.{u + 1} Λ) P).map ((L((p₁)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app K))).app
        ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
  have hT := supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ) i jU hU K
  have hT₁ := (L((p₁)^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT
  have := isTriangulated_rightDerivedUpperShriek (Λ := Λ) ι
  refine isIso_map_derivedTensor_map_app_of_isZero (A := ModuleCat.{u + 1} Λ)
    (R(ι)^![ModuleCat.{u + 1} Λ]) _ hT₁ ?_
  -- the third object: `Rι^!(p₁^* Rj_{U*} K|_U ⊗ p₂^* M) = Rb₁^! Ri₁^!(…) = 0`
  have hz := isZero_rightDerivedUpperShriek_derivedTensor_lowerStar Λ aY aX p₂ p₁ hP.flip i jU hU
    i₁ gi hi hU₁ eU sqU M ((L((jU)^*[ModuleCat.{u + 1} Λ])).obj K)
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) P
  have : IsClosedImmersion (b₁ ≫ i₁) := hb₁ ▸ inferInstance
  have : IsClosedImmersion b₁ := IsClosedImmersion.of_comp b₁ i₁
  have : HasCompactification (b₁ ≫ i₁) := .of_eq hb₁.symm
  have : QuasiCompact (b₁ ≫ i₁) := by rw [hb₁]; infer_instance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ b₁ i₁
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) hb₁.symm
  exact ((R(b₁)^![ModuleCat.{u + 1} Λ]).map_isZero hz).of_iso (heq.app _ ≪≫ c.app _ ≪≫
    (R(b₁)^![ModuleCat.{u + 1} Λ]).mapIso ((R(i₁)^![ModuleCat.{u + 1} Λ]).mapIso
      ((β.app _).app _)))

omit [Finite Λ] [IsClosedImmersion i₁] in
include hi in
/-- The pullback along `p₁` of an object `Ri_! N` vanishes on every scheme over `X × Y` missing
the preimage `Z₁` of `Z`. -/
lemma isZero_leftDerivedUpperStar_leftDerivedUpperStar_rightDerivedLowerShriek
    (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {Q : Scheme.{u}} (v : Q ⟶ P) (hv : Disjoint (Set.range v.base) (Set.range i₁.base)) :
    IsZero ((L((v)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj N))) := by
  have hd : Disjoint (Set.range (v ≫ p₁).base) (Set.range i.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, rfl⟩ hy
    have : v.base y ∈ Set.range i₁.base := by
      rw [Scheme.range_snd_of_isPullback' hi]
      exact hy
    exact Set.disjoint_left.1 hv ⟨y, rfl⟩ this
  exact (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i N
    (v ≫ p₁) hd).of_iso ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v p₁).app _).symm

include hP hU hV hi hw sqU sqV hb₁ hb₂ in
/-- The product of supports `Φ : p₁^*(Ri_! Ri^! K) ⊗ p₂^*(Rw_! Rw^! L) ⟶ Rι_! Rι^!(p₁^*K ⊗ p₂^*L)`,
through the restrictions of supports along the projections, is an isomorphism. -/
theorem isIso_supportedRestriction_tensor_supportedProduct
    (h : Set.range ι.base = Set.range i₁.base ∩ Set.range w₁.base)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (derivedTensorHom (ModuleCat.{u + 1} Λ)
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₁ i i₁ gi hi K _ (Iso.refl _))
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₂ w w₁ gw hw L _ (Iso.refl _)) ≫
      supportedProduct (ModuleCat.{u + 1} Λ) i₁ w₁ ι h _ _) := by
  have hψ₁ := (existsUnique_supportedRestriction (ModuleCat.{u + 1} Λ) p₁ i i₁ gi hi K _
    (Iso.refl _)).exists.choose_spec
  have hψ₂ := (existsUnique_supportedRestriction (ModuleCat.{u + 1} Λ) p₂ w w₁ gw hw L _
    (Iso.refl _)).exists.choose_spec
  have hε : (derivedTensorHom (ModuleCat.{u + 1} Λ)
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₁ i i₁ gi hi K _ (Iso.refl _))
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₂ w w₁ gw hw L _ (Iso.refl _)) ≫
      supportedProduct (ModuleCat.{u + 1} Λ) i₁ w₁ ι h _ _) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).counit.app _ =
      derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((L((p₁)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app K))
        ((L((p₂)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) w).counit.app L)) := by
    rw [Category.assoc, supportedProduct_comp_counit, derivedTensorHom_comp]
    erw [supportedRestriction, supportedRestriction, hψ₁, hψ₂]
    congr 1 <;> exact Category.comp_id _
  -- `Rι^!` of the composite with the counit is an isomorphism
  have h₁ := isIso_rightDerivedUpperShriek_map_counit_tensor_left Λ aX aY p₁ p₂ hP i jU hU i₁ gi
    hi hU₁ eU sqU ι b₁ hb₁ K
    ((R(w)_![ModuleCat.{u + 1} Λ]).obj ((R(w)^![ModuleCat.{u + 1} Λ]).obj L))
  have h₂ := isIso_rightDerivedUpperShriek_map_tensor_counit_right Λ aX aY p₁ p₂ hP w jV hV w₁ gw
    hw hV₁ eV sqV ι b₂ hb₂ K L
  have h₃ : IsIso ((R(ι)^![ModuleCat.{u + 1} Λ]).map (derivedTensorHom (ModuleCat.{u + 1} Λ)
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app K))
      ((L((p₂)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) w).counit.app L)))) := by
    rw [derivedTensorHom, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  have hu := isIso_rightDerivedUpperShriekAdjunction_unit_app (ModuleCat.{u + 1} Λ) ι
    ((R(ι)^![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj L)))
  have hc : IsIso ((R(ι)^![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).counit.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj
          ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj L)))) := by
    generalize (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj L)) = N
    have e :=
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).right_triangle_components N
    have : IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).unit.app
        ((R(ι)^![ModuleCat.{u + 1} Λ]).obj N) ≫ (R(ι)^![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).counit.app N)) := by
      rw [e]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).unit.app
      ((R(ι)^![ModuleCat.{u + 1} Λ]).obj N)) _
  rw [← hε, Functor.map_comp] at h₃
  have hΦ := (isIso_comp_right_iff _ _).1 h₃
  -- both ends are supported on `T`, where `Rι_! Rι^!` is the identity
  have hS : IsZero ((L((ι.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)))).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(w)_![ModuleCat.{u + 1} Λ]).obj ((R(w)^![ModuleCat.{u + 1} Λ]).obj L))))) :=
    isZero_leftDerivedUpperStar_derivedTensor_of_disjoint _ i₁ w₁ ι h
      (fun v hv ↦ isZero_leftDerivedUpperStar_leftDerivedUpperStar_rightDerivedLowerShriek Λ p₁
        i i₁ gi hi _ v hv)
      (fun v hv ↦ isZero_leftDerivedUpperStar_leftDerivedUpperStar_rightDerivedLowerShriek Λ p₂
        w w₁ gw hw _ v hv)
      _ (disjoint_range_openComplement_ι ι)
  have := isIso_counit_app_of_isZero Λ ι _ hS
  have := isIso_counit_app_of_isZero Λ ι _ (isSupported_rightDerivedLowerShriek Λ ι
    ((R(ι)^![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) P).obj
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj L))))
  have hn := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).counit.naturality
    (derivedTensorHom (ModuleCat.{u + 1} Λ)
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₁ i i₁ gi hi K _ (Iso.refl _))
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₂ w w₁ gw hw L _ (Iso.refl _)) ≫
      supportedProduct (ModuleCat.{u + 1} Λ) i₁ w₁ ι h _ _)
  have h₄ : IsIso ((R(ι)_![ModuleCat.{u + 1} Λ]).map ((R(ι)^![ModuleCat.{u + 1} Λ]).map
      (derivedTensorHom (ModuleCat.{u + 1} Λ)
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₁ i i₁ gi hi K _ (Iso.refl _))
        (supportedRestriction (ModuleCat.{u + 1} Λ) p₂ w w₁ gw hw L _ (Iso.refl _)) ≫
      supportedProduct (ModuleCat.{u + 1} Λ) i₁ w₁ ι h _ _)) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).counit.app _) := inferInstance
  erw [hn] at h₄
  exact (isIso_comp_left_iff _ _).1 h₄

end Local
section Main

variable {Z W Z₁ W₁ T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : W ⟶ Y)
  [IsClosedImmersion j] (i₁ : Z₁ ⟶ P) (gi : Z₁ ⟶ Z) (hi : IsPullback gi i₁ i p₁)
  (j₁ : W₁ ⟶ P) (gj : W₁ ⟶ W) (hj : IsPullback gj j₁ j p₂) [IsClosedImmersion i₁]
  [IsClosedImmersion j₁] (ι : T ⟶ P) [IsClosedImmersion ι]
  (h : Set.range ι.base = Set.range i₁.base ∩ Set.range j₁.base)
  (b₁ : T ⟶ Z₁) (hb₁ : b₁ ≫ i₁ = ι) (b₂ : T ⟶ W₁) (hb₂ : b₂ ≫ j₁ = ι)

include hP hi hj hb₁ hb₂ in
/-- Blueprint `lem-pur-kunneth-supported`: Künneth with supports

Let `X`, `Y` be schemes of finite type over a separably closed field `k`, `P = X ×_k Y`, and
`Z ⊆ X`, `W ⊆ Y` closed subschemes, with preimages `Z₁ = Z × Y`, `W₁ = X × W` in `P` and
`ι : T ⟶ P` a closed immersion onto `Z × W` (factoring through both). For all
`K ∈ D(X_ét, Λ)` and `L ∈ D(Y_ét, Λ)` the supported exterior product
(`AlgebraicGeometry.Etale.supportedExteriorProduct`)

`RΓ_Z(X, K) ⊗ᴸ RΓ_W(Y, L) ⟶ RΓ_{Z × W}(X ×_k Y, K ⊠ L)`

is an isomorphism. The cohomology objects are taken in `D((Spec k)_ét)`, equivalent to `D(Λ)`
as `k` is separably closed. -/
theorem isIso_supportedExteriorProduct [IsSepClosed k]
    [QuasiCompact i.openComplement.ι] [QuasiCompact j.openComplement.ι]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (supportedExteriorProduct Λ aX aY p₁ p₂ hP.w.symm i j i₁ gi hi j₁ gj hj ι h K L) := by
  have h₁ := isIso_kunnethMap_of_isSepClosed Λ aX aY p₁ p₂ hP
    ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K))
    ((R(j)_![ModuleCat.{u + 1} Λ]).obj ((R(j)^![ModuleCat.{u + 1} Λ]).obj L))
  have h₂ := isIso_supportedRestriction_tensor_supportedProduct Λ aX aY p₁ p₂ hP i
    i.openComplement.ι i.range_eq_compl_range_openComplement_ι j j.openComplement.ι
    j.range_eq_compl_range_openComplement_ι i₁ gi hi j₁ gj hj
    (p₁ ⁻¹ᵁ i.openComplement).ι (p₁ ∣_ i.openComplement)
    (isPullback_morphismRestrict p₁ i.openComplement).flip
    (p₂ ⁻¹ᵁ j.openComplement).ι (p₂ ∣_ j.openComplement)
    (isPullback_morphismRestrict p₂ j.openComplement).flip ι b₁ hb₁ b₂ hb₂ h K L
  unfold supportedExteriorProduct
  infer_instance

end Main

end AlgebraicGeometry.Etale
