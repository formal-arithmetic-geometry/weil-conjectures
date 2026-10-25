/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction

/-!
# Naturality of the restriction triangle inside a closed support

The two maps of the restriction triangle

`RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F) ⟶ RΓ_{B ∩ C}(T, F)[1]`

of `AlgebraicGeometry.Etale.exists_distTriang_supportRestriction` (blueprint
`lem-pur-support-restriction-triangle`) are natural in `F`. Both are built from maps of supported
terms `Ri_! Ri^! F` which are characterised by their composite with a counit of `Ri_! ⊣ Ri^!`;
naturality follows from the uniqueness of these factorisations.

## Main statements

- `AlgebraicGeometry.Etale.supportedRestriction_naturality`
- `AlgebraicGeometry.Etale.supportedInclusion_naturality`
- `AlgebraicGeometry.Etale.supportInclusionMap_naturality`
- `AlgebraicGeometry.Etale.supportRestrictionMap_naturality`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Restriction

variable {U X Z Z' : Scheme.{u}}

/-- The pullback along `e : U ⟶ X` of a supported term `Ri_! Ri^! L` is supported on the base
change `Z'` of `Z`: it vanishes on the open complement of `i'`. -/
lemma isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_supported (e : U ⟶ X)
    (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i] [(R(i)_![A]).IsLeftAdjoint]
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsZero ((L((i'.openComplement.ι)^*[A])).obj
      ((L((e)^*[A])).obj ((R(i)_![A]).obj ((R(i)^![A]).obj L)))) := by
  refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint A i
    i.openComplement.ι (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left)
    (i'.openComplement.ι ≫ e) ?_ _).of_iso
      ((leftDerivedUpperStarComp A i'.openComplement.ι e).app _).symm
  rw [← compl_compl (Set.range i.openComplement.ι), ← i.range_eq_compl_range_openComplement_ι,
    Set.subset_compl_iff_disjoint_left, Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  apply x.2
  rw [Scheme.range_snd_of_isPullback hg]
  exact ⟨z, hx.symm⟩

/-- **Naturality of the restriction of supports.** For `φ : L₁ ⟶ L₂` on `X`, `φ' : L₁' ⟶ L₂'`
on `U` and identifications `τₖ : Le^* Lₖ ≅ Lₖ'` compatible with `φ` and `φ'`, the restrictions
of supports `Le^* (Ri_! Ri^! Lₖ) ⟶ Ri'_! Ri'^! Lₖ'`
(`AlgebraicGeometry.Etale.supportedRestriction`) commute with the maps induced by `φ` and
`φ'`. -/
theorem supportedRestriction_naturality (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [(R(i)_![A]).IsLeftAdjoint] [IsClosedImmersion i']
    [(R(i')_![A]).IsLeftAdjoint] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {L₁ L₂ : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L₁' L₂' : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (τ₁ : (L((e)^*[A])).obj L₁ ≅ L₁') (τ₂ : (L((e)^*[A])).obj L₂ ≅ L₂')
    (φ : L₁ ⟶ L₂) (φ' : L₁' ⟶ L₂') (h : (L((e)^*[A])).map φ ≫ τ₂.hom = τ₁.hom ≫ φ') :
    (L((e)^*[A])).map ((R(i)_![A]).map ((R(i)^![A]).map φ)) ≫
        supportedRestriction A e i i' g hg L₂ L₂' τ₂ =
      supportedRestriction A e i i' g hg L₁ L₁' τ₁ ≫
        (R(i')_![A]).map ((R(i')^![A]).map φ') := by
  have hε : (R(i)_![A]).map ((R(i)^![A]).map φ) ≫
      (rightDerivedUpperShriekAdjunction A i).counit.app L₂ =
        (rightDerivedUpperShriekAdjunction A i).counit.app L₁ ≫ φ :=
    (rightDerivedUpperShriekAdjunction A i).counit.naturality φ
  have hε' : (R(i')_![A]).map ((R(i')^![A]).map φ') ≫
      (rightDerivedUpperShriekAdjunction A i').counit.app L₂' =
        (rightDerivedUpperShriekAdjunction A i').counit.app L₁' ≫ φ' :=
    (rightDerivedUpperShriekAdjunction A i').counit.naturality φ'
  have h₁ := (existsUnique_supportedRestriction A e i i' g hg L₁ L₁' τ₁).exists.choose_spec
  have h₂ := (existsUnique_supportedRestriction A e i i' g hg L₂ L₂' τ₂).exists.choose_spec
  change supportedRestriction A e i i' g hg L₁ L₁' τ₁ ≫ _ = _ at h₁
  change supportedRestriction A e i i' g hg L₂ L₂' τ₂ ≫ _ = _ at h₂
  refine (existsUnique_comp_counit_of_isZero A i' i'.openComplement.ι
    i'.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_supported A e i i' g hg L₁)
    ((L((e)^*[A])).map ((rightDerivedUpperShriekAdjunction A i).counit.app L₁) ≫
      τ₁.hom ≫ φ')).unique ?_ ?_
  · rw [assoc, h₂, ← Functor.map_comp_assoc, hε, Functor.map_comp_assoc, h]
  · rw [assoc, hε', reassoc_of% h₁]

end Restriction

variable {T B C D : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T) (d : D ⟶ T)
  [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
  (hd : Set.range d.base = Set.range b.base ∩ Set.range c.base)

omit [IsClosedImmersion c] in
/-- The map of supported terms `Rd_! Rd^! F ⟶ Rb_! Rb^! F` for `D ⊆ B`
(`AlgebraicGeometry.Etale.supportedInclusion`) is natural in `F`. -/
theorem supportedInclusion_naturality {F F' : DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (φ : F ⟶ F') :
    supportedInclusion A b c d hd F ≫ (R(b)_![A]).map ((R(b)^![A]).map φ) =
      (R(d)_![A]).map ((R(d)^![A]).map φ) ≫ supportedInclusion A b c d hd F' := by
  have hεb : (R(b)_![A]).map ((R(b)^![A]).map φ) ≫
      (rightDerivedUpperShriekAdjunction A b).counit.app F' =
        (rightDerivedUpperShriekAdjunction A b).counit.app F ≫ φ :=
    (rightDerivedUpperShriekAdjunction A b).counit.naturality φ
  have hεd : (R(d)_![A]).map ((R(d)^![A]).map φ) ≫
      (rightDerivedUpperShriekAdjunction A d).counit.app F' =
        (rightDerivedUpperShriekAdjunction A d).counit.app F ≫ φ :=
    (rightDerivedUpperShriekAdjunction A d).counit.naturality φ
  refine (existsUnique_comp_counit_of_isZero A b b.openComplement.ι
    b.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_supported_of_inter A b c d hd F)
    ((rightDerivedUpperShriekAdjunction A d).counit.app F ≫ φ)).unique ?_ ?_
  · rw [assoc, hεb, supportedInclusion_comp_counit_assoc]
  · rw [assoc, supportedInclusion_comp_counit, hεd]

omit [IsClosedImmersion c] in
/-- Blueprint `lem-pur-support-restriction-triangle`: Restriction triangle inside a closed
support (naturality of the first map).

The inclusion of supports `RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F)`
(`AlgebraicGeometry.Etale.supportInclusionMap`) is natural in `F`. -/
theorem supportInclusionMap_naturality {F F' : DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (φ : F ⟶ F') :
    supportInclusionMap A b c d hd F ≫ (rightDerivedSectionsWithSupport A b).map φ =
      (rightDerivedSectionsWithSupport A d).map φ ≫ supportInclusionMap A b c d hd F' := by
  have h₁ : (rightDerivedSectionsWithSupport A d).map φ ≫
      ((rightDerivedSectionsWithSupportIso A d).app F').hom =
        ((rightDerivedSectionsWithSupportIso A d).app F).hom ≫
          (rightDerivedGlobalSections A T).map ((R(d)_![A]).map ((R(d)^![A]).map φ)) :=
    (rightDerivedSectionsWithSupportIso A d).hom.naturality φ
  have h₂ : (rightDerivedGlobalSections A T).map ((R(b)_![A]).map ((R(b)^![A]).map φ)) ≫
      ((rightDerivedSectionsWithSupportIso A b).app F').inv =
        ((rightDerivedSectionsWithSupportIso A b).app F).inv ≫
          (rightDerivedSectionsWithSupport A b).map φ :=
    (rightDerivedSectionsWithSupportIso A b).inv.naturality φ
  unfold supportInclusionMap
  rw [assoc, assoc, ← h₂, ← Functor.map_comp_assoc, supportedInclusion_naturality,
    Functor.map_comp_assoc, reassoc_of% h₁]

/-- The identification `supportRestrictionIso₃` of the last term of the restriction triangle is
natural in `F`. -/
theorem supportRestrictionIso₃_hom_naturality
    {F F' : DerivedCategory (Sheaf T.smallEtaleTopology A)} (φ : F ⟶ F') :
    (rightDerivedSectionsWithSupport A (pullback.snd b c.openComplement.ι)).map
        ((L((c.openComplement.ι)^*[A])).map φ) ≫ (supportRestrictionIso₃ A b c F').hom =
      (supportRestrictionIso₃ A b c F).hom ≫ (rightDerivedGlobalSections A T).map
        ((R((c.openComplement.ι)_*[A])).map ((L((c.openComplement.ι)^*[A])).map
          ((R(b)_![A]).map ((R(b)^![A]).map φ)))) := by
  set v := c.openComplement.ι
  set b' := pullback.snd b v
  have hpb := IsPullback.of_hasPullback b v
  have := isIso_supportedRestriction_of_isOpenImmersion A v b b' (pullback.fst b v) hpb F _
    (Iso.refl _)
  have := isIso_supportedRestriction_of_isOpenImmersion A v b b' (pullback.fst b v) hpb F' _
    (Iso.refl _)
  have hS := supportedRestriction_naturality A v b b' (pullback.fst b v) hpb (Iso.refl _)
    (Iso.refl _) φ ((L((v)^*[A])).map φ) (by simp)
  have hS' : inv (supportedRestriction A v b b' (pullback.fst b v) hpb F _ (Iso.refl _)) ≫
      (L((v)^*[A])).map ((R(b)_![A]).map ((R(b)^![A]).map φ)) =
      (R(b')_![A]).map ((R(b')^![A]).map ((L((v)^*[A])).map φ)) ≫
        inv (supportedRestriction A v b b' (pullback.fst b v) hpb F' _ (Iso.refl _)) := by
    rw [IsIso.inv_comp_eq, ← assoc, ← hS, assoc, IsIso.hom_inv_id, comp_id]
  have h₁ : (rightDerivedSectionsWithSupport A b').map ((L((v)^*[A])).map φ) ≫
      ((rightDerivedSectionsWithSupportIso A b').app _).hom =
        ((rightDerivedSectionsWithSupportIso A b').app _).hom ≫
          (rightDerivedGlobalSections A _).map
            ((R(b')_![A]).map ((R(b')^![A]).map ((L((v)^*[A])).map φ))) :=
    (rightDerivedSectionsWithSupportIso A b').hom.naturality ((L((v)^*[A])).map φ)
  have h₃ : (rightDerivedGlobalSections A _).map
      ((L((v)^*[A])).map ((R(b)_![A]).map ((R(b)^![A]).map φ))) ≫
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A v).app _).inv =
        ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A v).app _).inv ≫
          (rightDerivedGlobalSections A T).map ((R((v)_*[A])).map ((L((v)^*[A])).map
            ((R(b)_![A]).map ((R(b)^![A]).map φ)))) :=
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A v).inv.naturality _
  have hdef : ∀ (G : DerivedCategory (Sheaf T.smallEtaleTopology A))
      [IsIso (supportedRestriction A v b b' (pullback.fst b v) hpb G _ (Iso.refl _))],
      (supportRestrictionIso₃ A b c G).hom =
        ((rightDerivedSectionsWithSupportIso A b').app _).hom ≫
          (rightDerivedGlobalSections A _).map
            (inv (supportedRestriction A v b b' (pullback.fst b v) hpb G _ (Iso.refl _))) ≫
          ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A v).app _).inv :=
    fun _ _ ↦ rfl
  rw [hdef, hdef, assoc, assoc]
  rw [← h₃, ← Functor.map_comp_assoc, hS', Functor.map_comp_assoc, reassoc_of% h₁]

/-- Blueprint `lem-pur-support-restriction-triangle`: Restriction triangle inside a closed
support (naturality of the second map).

The restriction `RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F)` to the open complement `V` of `C`
(`AlgebraicGeometry.Etale.supportRestrictionMap`) is natural in `F`. -/
theorem supportRestrictionMap_naturality
    {F F' : DerivedCategory (Sheaf T.smallEtaleTopology A)} (φ : F ⟶ F') :
    supportRestrictionMap A b c F ≫
        (rightDerivedSectionsWithSupport A (pullback.snd b c.openComplement.ι)).map
          ((L((c.openComplement.ι)^*[A])).map φ) =
      (rightDerivedSectionsWithSupport A b).map φ ≫ supportRestrictionMap A b c F' := by
  set v := c.openComplement.ι
  have h₁ : (rightDerivedSectionsWithSupport A b).map φ ≫
      ((rightDerivedSectionsWithSupportIso A b).app F').hom =
        ((rightDerivedSectionsWithSupportIso A b).app F).hom ≫
          (rightDerivedGlobalSections A T).map ((R(b)_![A]).map ((R(b)^![A]).map φ)) :=
    (rightDerivedSectionsWithSupportIso A b).hom.naturality φ
  have h₂ : (R(b)_![A]).map ((R(b)^![A]).map φ) ≫
      (derivedUpperStarLowerStarAdjunction A v).unit.app ((R(b)_![A]).obj ((R(b)^![A]).obj F')) =
        (derivedUpperStarLowerStarAdjunction A v).unit.app
            ((R(b)_![A]).obj ((R(b)^![A]).obj F)) ≫
          (R((v)_*[A])).map ((L((v)^*[A])).map ((R(b)_![A]).map ((R(b)^![A]).map φ))) :=
    (derivedUpperStarLowerStarAdjunction A v).unit.naturality _
  have h₃ : (supportRestrictionIso₃ A b c F).inv ≫
      (rightDerivedSectionsWithSupport A (pullback.snd b v)).map ((L((v)^*[A])).map φ) =
        (rightDerivedGlobalSections A T).map ((R((v)_*[A])).map ((L((v)^*[A])).map
          ((R(b)_![A]).map ((R(b)^![A]).map φ)))) ≫ (supportRestrictionIso₃ A b c F').inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% (supportRestrictionIso₃_hom_naturality A b c φ),
      Iso.hom_inv_id, comp_id]
  have hdef : ∀ G : DerivedCategory (Sheaf T.smallEtaleTopology A),
      supportRestrictionMap A b c G = ((rightDerivedSectionsWithSupportIso A b).app G).hom ≫
        (rightDerivedGlobalSections A T).map ((derivedUpperStarLowerStarAdjunction A v).unit.app
          ((R(b)_![A]).obj ((R(b)^![A]).obj G))) ≫ (supportRestrictionIso₃ A b c G).inv :=
    fun _ ↦ rfl
  rw [hdef, hdef, assoc, assoc, h₃,← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc,
    reassoc_of% h₁]

end Etale

end AlgebraicGeometry
