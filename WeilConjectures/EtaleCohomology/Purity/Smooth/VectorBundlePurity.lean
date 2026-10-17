/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.EtaleCohomology.Purity.Smooth.VectorBundle
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarConjugation

/-!
# Vector-bundle purity

Let `π : V ⟶ S` be a vector bundle of rank `d` (`AlgebraicGeometry.VectorBundle`) with zero
section `z`, over a separated scheme of finite type over a field, on which the exponent of the
finite coefficient ring `Λ` is invertible. Then (blueprint `sk-prop-an`,
`thm-amb-vector-bundle-purity`)

`Rπ^! K ≅ Lπ^* K (d)[2d]`

for every `K ∈ D(S_ét, Λ)`, and in particular `ω_π = Rπ^! Λ_S ≅ Λ_V(d)[2d]`.

## Proof

By cohomological smoothness (`sk-prop-cohsm`) `Rπ^! K ≅ Lπ^* K ⊗ ω_π`, and `ω_π[-2d]` is a
locally constant sheaf of rank one; so everything comes down to `ω_π ≅ Λ_V(d)[2d]`. Over every
chart `π⁻¹ U ≅ 𝔸^d_U` this is affine-space purity (`cor-pur-affine-space-purity`). To glue the
local isomorphisms they are normalized along the zero section:

* the Thom isomorphism `Λ_S ≅ Rz^! (Λ_V(d)[2d])` (`AlgebraicGeometry.VectorBundle.isIso_thomClassMap`)
  and `Rz^! ω_π ≅ R(π ∘ z)^! Λ_S = Λ_S` give, through the co-projection formula for `z`, the
  section invariant `Lz^* ω_π ≅ Λ_S(d)[2d]`
  (`AlgebraicGeometry.VectorBundle.nonempty_iso_sectionInvariant`);
* every local isomorphism can be modified, by an automorphism pulled back from the base, so that
  its restriction to the zero section is the restriction of that global one
  (`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_map_eq`);
* two normalized local isomorphisms agree on the overlap of two charts, whose fibres are
  connected and meet the zero section
  (`AlgebraicGeometry.Etale.iso_ext_of_leftDerivedUpperStar_map_eq`);
* morphisms between sheaves placed in degree zero glue along open covers
  (`AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`).

## Main statements

- `AlgebraicGeometry.VectorBundle.nonempty_iso_sectionInvariant`: `Lz^* ω_π ≅ Λ_S(d)[2d]`.
- `AlgebraicGeometry.VectorBundle.nonempty_iso_dualizingComplex`: `ω_π ≅ Λ_V(d)[2d]`.
- `AlgebraicGeometry.VectorBundle.nonempty_iso_rightDerivedUpperShriek`: vector-bundle purity,
  `Rπ^! K ≅ Lπ^* K (d)[2d]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- An object `W` of `D(X_ét, A)` with `N ⊗ W ≅ 𝟙` is isomorphic to every `T` with
`T ⊗ N ≅ 𝟙`: `W ≅ (T ⊗ N) ⊗ W ≅ T ⊗ (N ⊗ W) ≅ T`. -/
lemma Etale.nonempty_iso_of_derivedTensor_iso {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    {N T W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e₁ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).obj N ≅ constantComplex Λ X)
    (e₂ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj N).obj W ≅ constantComplex Λ X) :
    Nonempty (W ≅ T) :=
  ⟨(derivedTensorLeftUnitor _ X W).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e₁.symm).app W ≪≫
    derivedTensorAssociator _ X T N W ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj T).mapIso e₂ ≪≫
    derivedTensorRightUnitor _ X T⟩

namespace VectorBundle

variable {V S : Scheme.{u}} {d : ℕ} {π : V ⟶ S} (E : VectorBundle d π)

/-! ### The section invariant -/

section SectionInvariant

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] [HasCompactification π]

/-- `Rz^! ω_π ≅ R(π ∘ z)^! Λ_S = Λ_S`. -/
lemma nonempty_iso_rightDerivedUpperShriek_dualizingComplex :
    Nonempty ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj
      (dualizingComplex (ModuleCat.{u + 1} Λ) π) ≅ constantComplex Λ S) := by
  have := E.isAffineHom
  have : HasCompactification (E.zero ≫ π) := .of_eq E.zero_comp.symm
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ E.zero π
  obtain ⟨h⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) E.zero_comp
  exact ⟨(c.app _).symm ≪≫ h.app _ ≪≫
    (rightDerivedUpperShriekIsoOfIso _ (Iso.refl S)).app _ ≪≫
      leftDerivedUpperStarConstantComplexIso Λ (𝟙 S)⟩

/-- Blueprint `sk-prop-an`: the *section invariant* of a vector bundle is the Tate twist,

`𝒞(π, z) = Lz^* ω_π ≅ Λ_S(d)[2d]`.

By the co-projection formula for the closed immersion `z` and the invertible objects `ω_π` and
`Λ_V(d)[2d]`, with `N = Rz^! Λ_V`,
`Λ_S ≅ Rz^! ω_π ≅ N ⊗ Lz^* ω_π` and `Λ_S ≅ Rz^! Λ_V(d)[2d] ≅ N ⊗ Λ_S(d)[2d]`, the latter by the
Thom isomorphism (`AlgebraicGeometry.VectorBundle.isIso_thomClassMap`). -/
theorem nonempty_iso_sectionInvariant :
    Nonempty (sectionInvariant Λ π E.zero ≅ (tateObject Λ S d)⟦2 * (d : ℤ)⟧) := by
  have : HasInvertibleExponent Λ S := .of_hom E.zero
  have := E.smoothOfRelativeDimension
  obtain ⟨Mω, ⟨eω'⟩, ⟨eω⟩⟩ := isInvertible_dualizingComplex Λ π (d := d)
  obtain ⟨MX, ⟨eX'⟩, ⟨eX⟩⟩ := (isInvertible_tateObject Λ V d).shift (2 * (d : ℤ))
  obtain ⟨ω₀⟩ := E.nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ
  have := E.isIso_thomClassMap Λ
  let cX := (derivedTensorRightCompRightDerivedUpperShriekIso Λ E.zero _ MX eX eX').app
    (constantComplex Λ V)
  let cω := (derivedTensorRightCompRightDerivedUpperShriekIso Λ E.zero _ Mω eω eω').app
    (constantComplex Λ V)
  let N := (R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ V)
  let e₂ : ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj N).obj (sectionInvariant Λ π E.zero) ≅
      constantComplex Λ S :=
    cω.symm ≪≫ (R(E.zero)^![ModuleCat.{u + 1} Λ]).mapIso (derivedTensorLeftUnitor _ V _) ≪≫ ω₀
  let e₁ : ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj N).obj
      ((tateObject Λ S d)⟦2 * (d : ℤ)⟧) ≅ constantComplex Λ S :=
    ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj N).mapIso
        (leftDerivedUpperStarTateShiftIso Λ E.zero d).symm ≪≫ cX.symm ≪≫
      (R(E.zero)^![ModuleCat.{u + 1} Λ]).mapIso (derivedTensorLeftUnitor _ V _) ≪≫
        (asIso (E.thomClassMap Λ)).symm
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) S
  exact nonempty_iso_of_derivedTensor_iso ((β.app _).app N ≪≫ e₁) e₂

end SectionInvariant

/-! ### Gluing along the charts -/

section Gluing

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The overlap of two charts maps to the first. -/
noncomputable abbrev overlapLeft (i j : E.ι) :
    (π ⁻¹ᵁ (E.U i ⊓ E.U j)).toScheme ⟶ (π ⁻¹ᵁ E.U i).toScheme :=
  V.homOfLE (π.preimage_mono inf_le_left)

/-- The overlap of two charts maps to the second. -/
noncomputable abbrev overlapRight (i j : E.ι) :
    (π ⁻¹ᵁ (E.U i ⊓ E.U j)).toScheme ⟶ (π ⁻¹ᵁ E.U j).toScheme :=
  V.homOfLE (π.preimage_mono inf_le_right)

/-- The restriction of a normalized local isomorphism to the overlap of two charts, then to the
zero section, is the restriction of the global one. -/
lemma restrictPullbackHom_zeroRes_overlap
    {A B : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (β : (L((E.zero)^*[ModuleCat.{u + 1} Λ])).obj A ⟶ (L((E.zero)^*[ModuleCat.{u + 1} Λ])).obj B)
    (i : E.ι) (W : S.Opens) (hW : W ≤ E.U i)
    (δ : (L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj A ⟶
      (L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj B)
    (hδ : restrictPullbackHom (E.zeroRes (E.U i)) (π ⁻¹ᵁ E.U i).ι ((E.U i).ι ≫ E.zero)
      (E.zeroRes_ι _).symm δ = restrictPullbackHom (E.U i).ι E.zero _ rfl β) :
    restrictPullbackHom (E.zeroRes W) (π ⁻¹ᵁ W).ι (W.ι ≫ E.zero) (E.zeroRes_ι _).symm
        (restrictPullbackHom (V.homOfLE (π.preimage_mono hW)) (π ⁻¹ᵁ E.U i).ι (π ⁻¹ᵁ W).ι
          (Scheme.homOfLE_ι _ _).symm δ) =
      restrictPullbackHom W.ι E.zero _ rfl β := by
  have h₁ := restrictPullbackHom_restrictPullbackHom (E.zeroRes W)
    (V.homOfLE (π.preimage_mono hW)) (π ⁻¹ᵁ E.U i).ι (π ⁻¹ᵁ W).ι (Scheme.homOfLE_ι _ _).symm
    (S.homOfLE hW ≫ E.zeroRes (E.U i)) (E.zeroRes_homOfLE hW).symm (W.ι ≫ E.zero)
    (E.zeroRes_ι _).symm δ
  have h₂ := restrictPullbackHom_restrictPullbackHom (S.homOfLE hW) (E.zeroRes (E.U i))
    (π ⁻¹ᵁ E.U i).ι ((E.U i).ι ≫ E.zero) (E.zeroRes_ι _).symm
    (S.homOfLE hW ≫ E.zeroRes (E.U i)) rfl (W.ι ≫ E.zero)
    (by rw [Scheme.homOfLE_ι_assoc]) δ
  have h₃ := restrictPullbackHom_restrictPullbackHom (S.homOfLE hW) (E.U i).ι E.zero
    ((E.U i).ι ≫ E.zero) rfl W.ι (Scheme.homOfLE_ι _ _).symm (W.ι ≫ E.zero)
    (by rw [Scheme.homOfLE_ι_assoc]) β
  rw [h₁, ← h₂, hδ, h₃]

/-- **Gluing along the charts.** Let `A, B ∈ D(V_ét, Λ)` be sheaves placed in degree zero, with
`A` invertible and, over every chart, a pullback from the base. If `A ≅ B` over every chart and
`Lz^* A ≅ Lz^* B` along the zero section, then `A ≅ B`. -/
theorem nonempty_iso_of_charts
    {A B : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (eA : A ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eB : B ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G)
    (hA : DerivedCategory.isInvertible Λ V A)
    (hloc : ∀ i, Nonempty ((L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj A ≅
      (L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj B))
    (hpb : ∀ i, ∃ C : _root_.DerivedCategory
        (Sheaf (E.U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty ((L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj A ≅
        (L((π ∣_ E.U i)^*[ModuleCat.{u + 1} Λ])).obj C))
    (hz : Nonempty ((L((E.zero)^*[ModuleCat.{u + 1} Λ])).obj A ≅
      (L((E.zero)^*[ModuleCat.{u + 1} Λ])).obj B)) :
    Nonempty (A ≅ B) := by
  obtain ⟨β⟩ := hz
  -- the local isomorphisms, normalized along the zero section
  have hnorm : ∀ i, ∃ δ : (L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj A ≅
      (L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj B,
      restrictPullbackHom (E.zeroRes (E.U i)) (π ⁻¹ᵁ E.U i).ι ((E.U i).ι ≫ E.zero)
        (E.zeroRes_ι _).symm δ.hom = restrictPullbackHom (E.U i).ι E.zero _ rfl β.hom := by
    intro i
    obtain ⟨C, ⟨φ⟩⟩ := hpb i
    let c := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (E.zeroRes (E.U i))
      (π ⁻¹ᵁ E.U i).ι ((E.U i).ι ≫ E.zero) (E.zeroRes_ι _).symm
    obtain ⟨δ, hδ⟩ := exists_iso_leftDerivedUpperStar_map_eq (π ∣_ E.U i) (E.zeroRes (E.U i))
      (E.zeroRes_comp_morphismRestrict _) φ (hloc i).some
      ((c.app A).symm ≪≫ restrictPullbackIso (E.U i).ι E.zero _ rfl β ≪≫ c.app B)
    refine ⟨δ, ?_⟩
    simp only [restrictPullbackHom, hδ]
    simp [c, restrictPullbackHom]
  choose δ hδ using hnorm
  -- normalized local isomorphisms agree on the overlaps of the charts
  have hP : ∀ i j, restrictPullbackHom (E.overlapLeft i j) (π ⁻¹ᵁ E.U i).ι
      (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι (Scheme.homOfLE_ι _ _).symm (δ i).hom =
      restrictPullbackHom (E.overlapRight i j) (π ⁻¹ᵁ E.U j).ι
      (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι (Scheme.homOfLE_ι _ _).symm (δ j).hom := by
    intro i j
    have hA' := DerivedCategory.isInvertible.leftDerivedUpperStar (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι hA
    have h := iso_ext_of_leftDerivedUpperStar_map_eq (E.zeroRes (E.U i ⊓ E.U j))
      (E.exists_isPreconnected_zeroRes _) hA'
      (restrictPullbackIso (E.overlapLeft i j) _ _ (Scheme.homOfLE_ι _ _).symm (δ i))
      (restrictPullbackIso (E.overlapRight i j) _ _ (Scheme.homOfLE_ι _ _).symm (δ j))
      (map_eq_of_restrictPullbackHom_eq _ _ _ (E.zeroRes_ι _).symm (by
        simp only [restrictPullbackIso_hom]
        rw [E.restrictPullbackHom_zeroRes_overlap β.hom i _ inf_le_left _ (hδ i),
          E.restrictPullbackHom_zeroRes_overlap β.hom j _ inf_le_right _ (hδ j)]))
    exact congrArg Iso.hom h
  obtain ⟨γ, hγ⟩ := exists_hom_of_isOpenImmersion_cover eA eB (fun i ↦ (π ⁻¹ᵁ E.U i).ι)
    (fun x ↦ E.mem_range_frame_e x) (fun i ↦ (δ i).hom) (by
      intro i j W a b _ _ h
      have hr : Set.range (a ≫ (π ⁻¹ᵁ E.U i).ι).base ⊆
          Set.range (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι.base := by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have h₁ : (a ≫ (π ⁻¹ᵁ E.U i).ι).base y ∈ π ⁻¹ᵁ E.U i := by
          rw [Scheme.Hom.comp_apply]
          exact (a.base y).2
        have h₂ : (a ≫ (π ⁻¹ᵁ E.U i).ι).base y ∈ π ⁻¹ᵁ E.U j := by
          rw [h, Scheme.Hom.comp_apply]
          exact (b.base y).2
        exact ⟨h₁, h₂⟩
      let c := IsOpenImmersion.lift (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι _ hr
      have hc : c ≫ (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι = a ≫ (π ⁻¹ᵁ E.U i).ι :=
        IsOpenImmersion.lift_fac _ _ _
      have hca : a = c ≫ E.overlapLeft i j := by
        rw [← cancel_mono (π ⁻¹ᵁ E.U i).ι, Category.assoc, Scheme.homOfLE_ι, hc]
      have hcb : b = c ≫ E.overlapRight i j := by
        rw [← cancel_mono (π ⁻¹ᵁ E.U j).ι, Category.assoc, Scheme.homOfLE_ι, hc, h]
      have e₁ := restrictPullbackHom_restrictPullbackHom c (E.overlapLeft i j)
        (π ⁻¹ᵁ E.U i).ι (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι (Scheme.homOfLE_ι _ _).symm a hca
        (a ≫ (π ⁻¹ᵁ E.U i).ι) hc.symm (δ i).hom
      have e₂ := restrictPullbackHom_restrictPullbackHom c (E.overlapRight i j)
        (π ⁻¹ᵁ E.U j).ι (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι (Scheme.homOfLE_ι _ _).symm b hcb
        (a ≫ (π ⁻¹ᵁ E.U i).ι) hc.symm (δ j).hom
      rw [hP i j] at e₁
      exact e₁.symm.trans e₂)
  have : IsIso γ := isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ
    (fun i ↦ (π ⁻¹ᵁ E.U i).ι) (fun x ↦ by
      obtain ⟨i, y, hy⟩ := E.mem_range_frame_e x
      exact ⟨i, y, hy⟩) γ fun i ↦ by
    rw [hγ i]
    infer_instance
  exact ⟨asIso γ⟩

end Gluing

/-! ### Vector-bundle purity -/

section Purity

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] [HasCompactification π]
  {k : Type u} [Field k] (aS : S ⟶ Spec (.of k)) [IsSeparated aS] [LocallyOfFiniteType aS]

include aS in
/-- Over a chart `π⁻¹ U ≅ 𝔸^d_U`, the dualizing complex of `π` restricts to `Λ(d)[2d]`: by
smooth base change `ω_π` restricts to `ω_{π_U}`, which the chart identifies with the dualizing
complex of `𝔸^d_U`, and affine-space purity (`cor-pur-affine-space-purity`). -/
lemma nonempty_iso_leftDerivedUpperStar_dualizingComplex (i : E.ι) :
    Nonempty ((L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) π) ≅
      (tateObject Λ (π ⁻¹ᵁ E.U i).toScheme d)⟦2 * (d : ℤ)⟧) := by
  have := E.smoothOfRelativeDimension
  have := E.isAffineHom
  have : HasInvertibleExponent Λ (π ⁻¹ᵁ E.U i).toScheme := .of_hom (π ⁻¹ᵁ E.U i).ι
  have : HasInvertibleExponent Λ (E.U i).toScheme := .of_hom (E.zeroRestrict i)
  have sq : IsPullback (π ⁻¹ᵁ E.U i).ι (π ∣_ E.U i) π (E.U i).ι :=
    (isPullback_morphismRestrict π (E.U i)).flip
  have : HasCompactification (π ∣_ E.U i) := HasCompactification.of_isPullback sq
  obtain ⟨bc⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) π sq
  have hp : π ∣_ E.U i = (E.chart i).hom ≫ 𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i :=
    (E.chart_over i).symm
  have : HasCompactification ((E.chart i).hom ≫ 𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i) := .of_eq hp
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (ModuleCat.{u + 1} Λ) hp
  obtain ⟨comp⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (E.chart i).hom
    (𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i)
  obtain ⟨ωp⟩ := nonempty_iso_dualizingComplex_affineSpace Λ d (E.U i) ((E.U i).ι ≫ aS)
  exact ⟨bc.app _ ≪≫ (R(π ∣_ E.U i)^![ModuleCat.{u + 1} Λ]).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ _) ≪≫ heq.app _ ≪≫ comp.app _ ≪≫
    (rightDerivedUpperShriekIsoOfIso _ (E.chart i)).app _ ≪≫
    (L(((E.chart i).hom)^*[ModuleCat.{u + 1} Λ])).mapIso
      (ωp ≪≫ twistShiftConstantComplexIso Λ _ d) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ d⟩

include aS in
/-- Blueprint `sk-prop-an`: vector-bundle purity for the dualizing complex,

`ω_π = Rπ^! Λ_S ≅ Λ_V(d)[2d]`.

The sheaves `Λ_V(d)` and `ω_π[-2d]` (`thm-asd-smooth-tensor`) are isomorphic over every chart
(`AlgebraicGeometry.VectorBundle.nonempty_iso_leftDerivedUpperStar_dualizingComplex`) and along
the zero section (`AlgebraicGeometry.VectorBundle.nonempty_iso_sectionInvariant`), so they are
isomorphic (`AlgebraicGeometry.VectorBundle.nonempty_iso_of_charts`). -/
theorem nonempty_iso_dualizingComplex :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) π ≅ (tateObject Λ V d)⟦2 * (d : ℤ)⟧) := by
  have : HasInvertibleExponent Λ S := .of_hom E.zero
  have := E.smoothOfRelativeDimension
  set ω := dualizingComplex (ModuleCat.{u + 1} Λ) π
  obtain ⟨F, -, -, ⟨eF⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) V d
  obtain ⟨G, -, -, ⟨eG⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ π d
  let sh : ∀ {X : Scheme.{u}}
      (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (M⟦2 * (d : ℤ)⟧)⟦-(2 * (d : ℤ))⟧ ≅ M := fun M ↦
    (shiftFunctorCompIsoId _ (2 * (d : ℤ)) (-(2 * (d : ℤ))) (by ring)).app M
  obtain ⟨σ⟩ := E.nonempty_iso_sectionInvariant Λ
  obtain ⟨e⟩ := E.nonempty_iso_of_charts (Λ := Λ) (A := tateObject Λ V d)
    (B := ω⟦-(2 * (d : ℤ))⟧) eF ((shiftFunctor _ _).mapIso eG ≪≫ sh _)
    (isInvertible_tateObject Λ V d)
    (fun i ↦ by
      have : HasInvertibleExponent Λ (π ⁻¹ᵁ E.U i).toScheme := .of_hom (π ⁻¹ᵁ E.U i).ι
      obtain ⟨l⟩ := E.nonempty_iso_leftDerivedUpperStar_dualizingComplex Λ aS i
      exact ⟨leftDerivedUpperStarTateObjectIso _ d ≪≫ (sh _).symm ≪≫
        (shiftFunctor _ _).mapIso l.symm ≪≫
          (((L(((π ⁻¹ᵁ E.U i).ι)^*[ModuleCat.{u + 1} Λ])).commShiftIso _).app ω).symm⟩)
    (fun i ↦ by
      have : HasInvertibleExponent Λ (π ⁻¹ᵁ E.U i).toScheme := .of_hom (π ⁻¹ᵁ E.U i).ι
      have : HasInvertibleExponent Λ (E.U i).toScheme := .of_hom (E.zeroRestrict i)
      exact ⟨tateObject Λ (E.U i).toScheme d, ⟨leftDerivedUpperStarTateObjectIso _ d ≪≫
        (leftDerivedUpperStarTateObjectIso (π ∣_ E.U i) d).symm⟩⟩)
    ⟨leftDerivedUpperStarTateObjectIso _ d ≪≫ (sh _).symm ≪≫ (shiftFunctor _ _).mapIso σ.symm ≪≫
      (((L((E.zero)^*[ModuleCat.{u + 1} Λ])).commShiftIso _).app ω).symm⟩
  exact ⟨(shiftFunctorCompIsoId _ (-(2 * (d : ℤ))) (2 * (d : ℤ)) (by ring)).symm.app ω ≪≫
    (shiftFunctor _ _).mapIso e.symm⟩

include aS in
/-- Blueprint `thm-amb-vector-bundle-purity`: Vector-bundle purity before smooth orientation

Let `π : V ⟶ S` be a vector bundle of rank `d` over a separated scheme of finite type over a
field, on which the exponent of the finite coefficient ring `Λ` is invertible. For every complex
`K` of étale `Λ`-modules on `S`,

`Rπ^! K ≅ Lπ^* K (d)[2d]`.

This is the tensor formula `Rπ^! K ≅ Lπ^* K ⊗ ω_π` of cohomological smoothness
(`thm-asd-smooth-tensor`) with `ω_π ≅ Λ_V(d)[2d]`
(`AlgebraicGeometry.VectorBundle.nonempty_iso_dualizingComplex`). In the blueprint the
isomorphism is the adjoint of the integration map; here only its existence is recorded. -/
theorem nonempty_iso_rightDerivedUpperShriek
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(π)^![ModuleCat.{u + 1} Λ]).obj K ≅
      (twistShift Λ V d).obj ((L((π)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  have := E.smoothOfRelativeDimension
  obtain ⟨t⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ π d K
  obtain ⟨ω⟩ := E.nonempty_iso_dualizingComplex Λ aS
  exact ⟨t.symm ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) V).obj _).mapIso ω ≪≫
    (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj _).commShiftIso (2 * (d : ℤ))).app _⟩

end Purity

end VectorBundle

end AlgebraicGeometry
