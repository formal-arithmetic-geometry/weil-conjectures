/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.Mathlib.RingTheory.Ideal.Operations

/-!
# Vanishing of a section of a line bundle is compatible with pullback

A global section `s` of a sheaf of `𝒪ₓ`-modules `F` on a scheme `X` *vanishes* at a point `x`
when its germ at `x` lies in `𝔪ₓ Fₓ` (`AlgebraicGeometry.Scheme.Modules.VanishesAt`). This file
proves that for an **invertible** sheaf of modules this notion is compatible with pullback: for
`a : X ⟶ Y` and `s` a global section of an invertible `𝒪ᵧ`-module `L`, the pullback `a^* s`
vanishes at `x` exactly when `s` vanishes at `a x`.

The proof has three ingredients.

* **Open immersions.** Pulling back along an open immersion does not change stalks, so vanishing
  is unchanged. This is `vanishesAt_sectionsPullback_iff_of_isOpenImmersion`, obtained from the
  comparison `AlgebraicGeometry.Scheme.Modules.restrictStalkEquiv` of the stalks of a
  restriction together with `restrictFunctorIsoPullback_hom_app_app_top`, which identifies the
  pullback of a global section along an open immersion with its restriction.
* **A globally trivialised sheaf.** If `L` is trivialised by a global section `t`, that is if
  multiplication by `t` is an isomorphism `𝒪ᵧ ≅ L`, then every global section of `L` is `g • t`
  for a unique global function `g`; since `t` vanishes nowhere
  (`AlgebraicGeometry.Scheme.Modules.not_vanishesAt_of_isIso_homOfSectionTop`), the section
  `g • t` vanishes exactly outside the basic open subset of `g`. Multiplication by `t` pulls
  back to multiplication by `a^* t`
  (`AlgebraicGeometry.Scheme.Modules.map_homOfSectionTop`), so the same description holds
  upstairs with `g` replaced by its pullback, and the basic open subsets correspond.
  This is `vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop`.
* **Localisation.** An invertible sheaf is trivialised by a section over some open `W` around
  `a x`, and the commuting triangle `(a ∣_ W) ≫ W.ι = (a ⁻¹ᵁ W).ι ≫ a` lets the general case be
  read off from the two previous ones through
  `AlgebraicGeometry.Scheme.Modules.pullbackTriangle`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff`: **vanishing of a section
  of a line bundle is compatible with pullback.**
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff_of_isOpenImmersion`: the
  same statement for an arbitrary sheaf of modules and an open immersion.
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop`:
  the same statement for a sheaf of modules trivialised by a global section.
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_of_iso`: vanishing is invariant under an
  isomorphism of sheaves of modules.
- `AlgebraicGeometry.Scheme.Modules.not_vanishesAt_of_isIso_homOfSectionTop`: a global section
  trivialising a sheaf of modules vanishes at no point.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **Vanishing at a point is invariant under an isomorphism** of sheaves of modules: an
isomorphism is linear on the stalk at `x`, hence carries `𝔪ₓ Mₓ` onto `𝔪ₓ Nₓ`. -/
lemma vanishesAt_iff_of_iso {M N : X.Modules} (e : M ≅ N) (m : Γ(M, ⊤)) (x : X) :
    N.VanishesAt (Hom.app e.hom ⊤ m) x ↔ M.VanishesAt m x := by
  have hgerm : N.presheaf.germ ⊤ x trivial (Hom.app e.hom ⊤ m)
      = e.hom.stalkMap x (M.presheaf.germ ⊤ x trivial m) :=
    (Hom.germ_stalkMap_apply e.hom (U := ⊤) x trivial m).symm
  rw [vanishesAt_iff, vanishesAt_iff, hgerm]
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.mem_smul_top_of_semilinear (RingHom.id _)
    (AddMonoidHom.mk' (fun z ↦ e.hom.stalkMap x z) (fun _ _ ↦ map_add _ _ _))
    (fun r z ↦ Hom.stalkMap_smul e.hom x r z) _ _ (fun r hr ↦ hr) h⟩
  have key := Submodule.mem_smul_top_of_semilinear (RingHom.id (X.presheaf.stalk x))
    (AddMonoidHom.mk' (fun z ↦ e.inv.stalkMap x z) (fun _ _ ↦ map_add _ _ _))
    (fun r z ↦ Hom.stalkMap_smul e.inv x r z)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (fun r hr ↦ hr) h
  simp only [AddMonoidHom.mk'_apply] at key
  rwa [← Hom.stalkMap_comp_apply, e.hom_inv_id, Hom.stalkMap_id,
    ConcreteCategory.id_apply] at key

/-- A global section of `F`, read as a global section of the restriction of `F` along an open
immersion `j`: the sections of `F.restrict j` over `⊤` are the sections of `F` over the image
of `⊤`, so this is a restriction map of `F`. -/
noncomputable def restrictSectionTop (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (s : Γ(F, ⊤)) : Γ((restrictFunctor j).obj F, ⊤) :=
  F.presheaf.map (homOfLE (j.image_preimage_le ⊤)).op s

/-- **The comparison between restriction and pullback along an open immersion, read on global
sections**: the isomorphism `F|_Y ≅ j^* F` of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` carries the restriction of a
global section of `F` to its pullback. Both are the unit of the respective adjunction, so this
is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`. -/
lemma restrictFunctorIsoPullback_hom_app_app_top (j : Y ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (s : Γ(F, ⊤)) :
    Hom.app ((restrictFunctorIsoPullback j).hom.app F) ⊤ (restrictSectionTop j F s)
      = sectionsPullback j F s := by
  have h := congrArg (fun φ : F ⟶ (pushforward j).obj ((pullback j).obj F) ↦
      ConcreteCategory.hom (Hom.app φ ⊤) s)
    (Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
      (pullbackPushforwardAdjunction j) F)
  simp only [Hom.comp_app, restrictAdjunction_unit_app_app, pushforward_map_app,
    ConcreteCategory.comp_apply] at h
  have hid := ConcreteCategory.congr_hom
    (Scheme.presheaf_map_homOfLE_preimage_top_eq_id ((pullback j).obj F).presheaf j)
    (((pullbackPushforwardAdjunction j).unit.app F).app ⊤ s)
  rw [restrictSectionTop, restrictFunctorIsoPullback,
    sectionsPullback_apply j F s (homOfLE (by simp : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ ⊤)), hid]
  exact h

/-- **Vanishing is compatible with restriction to an open subscheme.** Restriction along an
open immersion does not change stalks
(`AlgebraicGeometry.Scheme.Modules.restrictStalkEquiv`), and the comparison is semilinear over
an isomorphism of local rings, so it matches the two maximal ideals. -/
lemma vanishesAt_restrictSectionTop_iff (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (s : Γ(F, ⊤)) (y : Y) :
    ((restrictFunctor j).obj F).VanishesAt (restrictSectionTop j F s) y ↔
      F.VanishesAt s (j.base y) := by
  have hg : restrictStalkEquiv j y F
      (((restrictFunctor j).obj F).presheaf.germ ⊤ y trivial (restrictSectionTop j F s))
      = F.presheaf.germ ⊤ (j.base y) trivial s :=
    (restrictStalkEquiv_germ j y F (U := ⊤) trivial (restrictSectionTop j F s)).trans
      (F.presheaf.germ_res_apply _ _ _ s)
  have hmem : ∀ r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      ConcreteCategory.hom
          (inv (j.stalkMap y) : Y.presheaf.stalk y ⟶ X.presheaf.stalk (j.base y)) r ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base y)) := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
    refine fun hu ↦ hr ?_
    have := hu.map (ConcreteCategory.hom (j.stalkMap y))
    rwa [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply] at this
  have hmem' : ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base y)),
      ConcreteCategory.hom (j.stalkMap y) r ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
    refine fun hu ↦ hr ?_
    have := hu.map (ConcreteCategory.hom
      (inv (j.stalkMap y) : Y.presheaf.stalk y ⟶ X.presheaf.stalk (j.base y)))
    rwa [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply] at this
  rw [vanishesAt_iff, vanishesAt_iff, ← hg]
  refine ⟨fun h ↦ Submodule.mem_smul_top_of_semilinear _
    (restrictStalkEquiv j y F).toAddMonoidHom
    (fun r z ↦ restrictStalkEquiv_smul j y F r z) _ _ hmem h, fun h ↦ ?_⟩
  have hsym : ∀ (r : X.presheaf.stalk (j.base y)) (w : F.presheaf.stalk (j.base y)),
      (restrictStalkEquiv j y F).symm.toAddMonoidHom (r • w)
        = ConcreteCategory.hom (j.stalkMap y) r •
          (restrictStalkEquiv j y F).symm.toAddMonoidHom w := by
    intro r w
    refine (restrictStalkEquiv j y F).injective ?_
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [AddEquiv.apply_symm_apply, restrictStalkEquiv_smul, AddEquiv.apply_symm_apply,
      ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
  have key := Submodule.mem_smul_top_of_semilinear
    (ConcreteCategory.hom (j.stalkMap y) :
      X.presheaf.stalk (j.base y) →+* Y.presheaf.stalk y)
    (restrictStalkEquiv j y F).symm.toAddMonoidHom hsym _ _ hmem' h
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    AddEquiv.symm_apply_apply] at key
  exact key

/-- **Vanishing is compatible with pullback along an open immersion.** -/
lemma vanishesAt_sectionsPullback_iff_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (s : Γ(F, ⊤)) (y : Y) :
    ((pullback j).obj F).VanishesAt (sectionsPullback j F s) y ↔ F.VanishesAt s (j.base y) := by
  refine Iff.trans ?_ (vanishesAt_restrictSectionTop_iff j F s y)
  rw [← restrictFunctorIsoPullback_hom_app_app_top j F s]
  exact vanishesAt_iff_of_iso ((restrictFunctorIsoPullback j).app F) _ y

/-- **A global section trivialising a sheaf of modules vanishes at no point**: it is the image of
the unit function, which vanishes nowhere because its basic open subset is all of `X`.

With `AlgebraicGeometry.Scheme.Modules.vanishesAt_smul_iff_notMem_basicOpen` this describes the
vanishing locus of every global section of a trivialised sheaf of modules. -/
lemma not_vanishesAt_of_isIso_homOfSectionTop {M : X.Modules} {t : Γ(M, ⊤)}
    (ht : IsIso (homOfSectionTop M t)) (x : X) : ¬ M.VanishesAt t x := by
  have h := vanishesAt_iff_of_iso (asIso (homOfSectionTop M t)) (1 : Γ(X, ⊤)) x
  rw [asIso_hom, homOfSectionTop_app_top, one_smul] at h
  rw [h, vanishesAt_structureModules_iff, not_not, Scheme.basicOpen_one]
  trivial

/-- **Vanishing is compatible with pullback, for a sheaf of modules trivialised by a global
section.** -/
lemma vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop (a : X ⟶ Y) {M : Y.Modules}
    {t : Γ(M, ⊤)} (ht : IsIso (homOfSectionTop M t)) (s : Γ(M, ⊤)) (x : X) :
    ((pullback a).obj M).VanishesAt (sectionsPullback a M s) x ↔ M.VanishesAt s (a.base x) := by
  obtain ⟨g, rfl⟩ : ∃ g : Γ(Y, ⊤), g • t = s := by
    obtain ⟨g, hg⟩ := (sectionsEquivOfIso (asIso (homOfSectionTop M t)) ⊤).surjective s
    exact ⟨g, (homOfSectionTop_app_top M t g).symm.trans hg⟩
  have ht' : IsIso (homOfSectionTop ((pullback a).obj M) (sectionsPullback a M t)) := by
    rw [← map_homOfSectionTop]
    infer_instance
  rw [sectionsPullback_smul,
    vanishesAt_smul_iff_notMem_basicOpen (not_vanishesAt_of_isIso_homOfSectionTop ht' x),
    vanishesAt_smul_iff_notMem_basicOpen (not_vanishesAt_of_isIso_homOfSectionTop ht _),
    not_iff_not, ← Scheme.preimage_basicOpen_top]
  rfl

/-- **Vanishing of a section of a line bundle is compatible with pullback**: a global section
`s` of an invertible sheaf of modules `L` on `Y` vanishes at `a x` exactly when its pullback
along `a : X ⟶ Y` vanishes at `x`.

The proof localises on an open `W ∋ a x` over which `L` is trivialised, and reads the pullback
of `s` along the two sides of the commuting square

```
             a ∣_ W
   a ⁻¹ᵁ W ──────────▶ W
      │                │
      │ (a ⁻¹ᵁ W).ι    │ W.ι
      ▼                ▼
      X ──────a──────▶ Y
```

through `AlgebraicGeometry.Scheme.Modules.pullbackTriangle`: down-then-right is the open
immersion case, right-then-down the trivialised case. -/
theorem vanishesAt_sectionsPullback_iff {L : Y.Modules} (hL : L.Invertible) (a : X ⟶ Y)
    (s : Γ(L, ⊤)) (x : X) :
    ((pullback a).obj L).VanishesAt (sectionsPullback a L s) x ↔ L.VanishesAt s (a.base x) := by
  obtain ⟨W, hW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom (a.base x)
  have hmi : IsIso (unitSmulRestrictHom m) := hm
  -- the restriction of `L` to `W` is trivialised by a global section
  obtain ⟨t, ht⟩ : ∃ t : Γ((pullback W.ι).obj L, ⊤),
      IsIso (homOfSectionTop ((pullback W.ι).obj L) t) := by
    refine ⟨Hom.app (asIso (unitSmulRestrictHom m) ≪≫
      (restrictFunctorIsoPullback W.ι).app L).hom ⊤ (oneSection W.toScheme ⊤), ?_⟩
    rw [← unitHomEquivTop_apply, ← unitHomEquivTop_symm_apply, Equiv.symm_apply_apply]
    infer_instance
  have hxV : x ∈ a ⁻¹ᵁ W := hW
  have hu : (a ∣_ W) ≫ W.ι = (a ⁻¹ᵁ W).ι ≫ a := morphismRestrict_ι a W
  -- restrict to the open subscheme `a ⁻¹ᵁ W` of `X`
  have h1 := (vanishesAt_sectionsPullback_iff_of_isOpenImmersion (a ⁻¹ᵁ W).ι
    ((pullback a).obj L) (sectionsPullback a L s) ⟨x, hxV⟩).symm
  -- read the two-step pullback along `(a ⁻¹ᵁ W).ι ≫ a` in two ways
  have h2 : ((pullback (a ⁻¹ᵁ W).ι).obj ((pullback a).obj L)).VanishesAt
        (sectionsPullback (a ⁻¹ᵁ W).ι _ (sectionsPullback a L s)) ⟨x, hxV⟩ ↔
      ((pullback ((a ⁻¹ᵁ W).ι ≫ a)).obj L).VanishesAt
        (sectionsPullback ((a ⁻¹ᵁ W).ι ≫ a) L s) ⟨x, hxV⟩ := by
    rw [← pullbackTriangle_hom_app_sectionsPullback
      (rfl : (a ⁻¹ᵁ W).ι ≫ a = (a ⁻¹ᵁ W).ι ≫ a) L s]
    exact (vanishesAt_iff_of_iso
      ((pullbackTriangle (rfl : (a ⁻¹ᵁ W).ι ≫ a = (a ⁻¹ᵁ W).ι ≫ a)).app L) _ ⟨x, hxV⟩).symm
  have h3 : ((pullback (a ∣_ W)).obj ((pullback W.ι).obj L)).VanishesAt
        (sectionsPullback (a ∣_ W) _ (sectionsPullback W.ι L s)) ⟨x, hxV⟩ ↔
      ((pullback ((a ⁻¹ᵁ W).ι ≫ a)).obj L).VanishesAt
        (sectionsPullback ((a ⁻¹ᵁ W).ι ≫ a) L s) ⟨x, hxV⟩ := by
    rw [← pullbackTriangle_hom_app_sectionsPullback hu L s]
    exact (vanishesAt_iff_of_iso ((pullbackTriangle hu).app L) _ ⟨x, hxV⟩).symm
  refine h1.trans (h2.trans (h3.symm.trans ?_))
  rw [vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop (a ∣_ W) ht,
    vanishesAt_sectionsPullback_iff_of_isOpenImmersion W.ι L s]
  have hpt : W.ι.base ((a ∣_ W).base ⟨x, hxV⟩) = a.base x := by simp
  rw [hpt]

end AlgebraicGeometry.Scheme.Modules
