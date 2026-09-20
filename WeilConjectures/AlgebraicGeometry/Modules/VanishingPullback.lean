/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial

/-!
# Vanishing of a section of a line bundle is compatible with pullback
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section Aux

/-- Transport of membership in `I • ⊤` along an additive map which is semilinear over a ring
map carrying `I` into `J`. -/
lemma mem_smul_top_of_semilinear {R S : Type u} [CommRing R] [CommRing S]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (σ : R →+* S) (f : M →+ N) (hf : ∀ (r : R) (m : M), f (r • m) = σ r • f m)
    (I : Ideal R) (J : Ideal S) (hIJ : ∀ r ∈ I, σ r ∈ J) {z : M}
    (hz : z ∈ I • (⊤ : Submodule R M)) : f z ∈ J • (⊤ : Submodule S N) := by
  refine Submodule.smul_induction_on hz (fun r hr n _ ↦ ?_) (fun p q hp hq ↦ ?_)
  · rw [hf]
    exact Submodule.smul_mem_smul (hIJ r hr) trivial
  · rw [map_add]
    exact Submodule.add_mem _ hp hq

end Aux

/-- **Vanishing at a point is invariant under an isomorphism** of sheaves of modules. -/
lemma vanishesAt_iff_of_iso {M N : X.Modules} (e : M ≅ N) (m : Γ(M, ⊤)) (x : X) :
    N.VanishesAt (Hom.app e.hom ⊤ m) x ↔ M.VanishesAt m x := by
  have hgerm : N.presheaf.germ ⊤ x trivial (Hom.app e.hom ⊤ m)
      = e.hom.stalkMap x (M.presheaf.germ ⊤ x trivial m) :=
    (Hom.germ_stalkMap_apply e.hom x trivial m).symm
  rw [vanishesAt_iff, vanishesAt_iff, hgerm]
  constructor
  · intro h
    have := mem_smul_top_of_semilinear (RingHom.id (X.presheaf.stalk x))
      (AddMonoidHom.mk' (fun z ↦ (inv (e.hom.stalkMap x)) z) (fun _ _ ↦ map_add _ _ _))
      (fun r z ↦ ?_) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (fun r hr ↦ hr) h
    · simpa [← ConcreteCategory.comp_apply] using this
    · exact (Hom.stalkMap_smul e.inv x r z).trans (by rw [← Hom.stalkMap_comp]; simp)
  · intro h
    refine mem_smul_top_of_semilinear (RingHom.id (X.presheaf.stalk x))
      (AddMonoidHom.mk' (fun z ↦ e.hom.stalkMap x z) (fun _ _ ↦ map_add _ _ _))
      (fun r z ↦ Hom.stalkMap_smul e.hom x r z) _ _ (fun r hr ↦ hr) h

/-- A global section of `F`, read as a global section of the restriction of `F` along an open
immersion. -/
def restrictSectionTop (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules) (s : Γ(F, ⊤)) :
    Γ((restrictFunctor j).obj F, ⊤) :=
  F.presheaf.map (homOfLE (j.image_preimage_le ⊤)).op s

/-- **The comparison between restriction and pullback along an open immersion, on global
sections**: the isomorphism `F|_Y ≅ j^* F` carries the restriction of a global section to its
pullback. -/
lemma restrictFunctorIsoPullback_hom_app_app_top (j : Y ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (s : Γ(F, ⊤)) :
    Hom.app ((restrictFunctorIsoPullback j).hom.app F) ⊤ (restrictSectionTop j F s)
      = sectionsPullback j F s := by
  have h := congrArg (fun φ : F ⟶ (pushforward j).obj ((pullback j).obj F) ↦
      ConcreteCategory.hom (Hom.app φ ⊤) s)
    (Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
      (pullbackPushforwardAdjunction j) F)
  simpa [restrictSectionTop, sectionsPullback, sectionsPullbackLE, restrictFunctorIsoPullback]
    using h

/-- **Vanishing is compatible with restriction to an open subscheme.** -/
lemma vanishesAt_restrictSectionTop_iff (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (s : Γ(F, ⊤)) (y : Y) :
    ((restrictFunctor j).obj F).VanishesAt (restrictSectionTop j F s) y ↔
      F.VanishesAt s (j.base y) := by
  have hg : restrictStalkEquiv j y F
      (((restrictFunctor j).obj F).presheaf.germ ⊤ y trivial (restrictSectionTop j F s))
      = F.presheaf.germ ⊤ (j.base y) trivial s := by
    rw [restrictStalkEquiv_germ]
    exact F.presheaf.germ_res_apply _ _ _ s
  have hunit (r : Y.presheaf.stalk y) :
      IsUnit r ↔ IsUnit ((inv (j.stalkMap y) : _ ⟶ _) r) := by
    refine ⟨fun hr ↦ hr.map (ConcreteCategory.hom (inv (j.stalkMap y))), fun hr ↦ ?_⟩
    have := hr.map (ConcreteCategory.hom (j.stalkMap y))
    rwa [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply] at this
  have hmem (r : Y.presheaf.stalk y) (hr : r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
      (inv (j.stalkMap y) : _ ⟶ _) r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base y)) := by
    rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
    exact fun hu ↦ hr ((hunit r).2 hu)
  have hmem' (r : X.presheaf.stalk (j.base y))
      (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base y))) :
      (j.stalkMap y : _ ⟶ _) r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
    exact fun hu ↦ hr (by
      have := hu.map (ConcreteCategory.hom (inv (j.stalkMap y)))
      rwa [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply] at this)
  rw [vanishesAt_iff, vanishesAt_iff, ← hg]
  constructor
  · intro h
    exact mem_smul_top_of_semilinear (ConcreteCategory.hom (inv (j.stalkMap y)))
      (restrictStalkEquiv j y F).toAddMonoidHom
      (fun r z ↦ restrictStalkEquiv_smul j y F r z) _ _ hmem h
  · intro h
    have key := mem_smul_top_of_semilinear (ConcreteCategory.hom (j.stalkMap y))
      (restrictStalkEquiv j y F).symm.toAddMonoidHom (fun r z ↦ ?_) _ _ hmem' h
    · simpa using key
    · refine (restrictStalkEquiv j y F).injective ?_
      rw [AddEquiv.toAddMonoidHom_eq_coe, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.apply_symm_apply, restrictStalkEquiv_smul, AddEquiv.apply_symm_apply,
        ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-- **Vanishing is compatible with pullback along an open immersion.** -/
lemma vanishesAt_sectionsPullback_iff_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (s : Γ(F, ⊤)) (y : Y) :
    ((pullback j).obj F).VanishesAt (sectionsPullback j F s) y ↔ F.VanishesAt s (j.base y) := by
  refine Iff.trans ?_ (vanishesAt_restrictSectionTop_iff j F s y)
  rw [← restrictFunctorIsoPullback_hom_app_app_top j F s]
  exact vanishesAt_iff_of_iso ((restrictFunctorIsoPullback j).app F) _ y

/-- **A section of a trivialised sheaf of modules vanishes exactly where its coefficient
does.** -/
lemma vanishesAt_smul_iff_notMem_basicOpen {M : X.Modules} {t : Γ(M, ⊤)}
    (ht : IsIso (homOfSectionTop M t)) (g : Γ(X, ⊤)) (x : X) :
    M.VanishesAt (g • t) x ↔ x ∉ X.basicOpen g := by
  have h := vanishesAt_iff_of_iso (asIso (homOfSectionTop M t)) g x
  rw [asIso_hom, homOfSectionTop_app_top] at h
  exact h.trans (vanishesAt_structureModules_iff x g)

/-- **Vanishing is compatible with pullback, for a sheaf of modules trivialised by a global
section.** -/
lemma vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop (a : X ⟶ Y) {M : Y.Modules}
    {t : Γ(M, ⊤)} (ht : IsIso (homOfSectionTop M t)) (s : Γ(M, ⊤)) (x : X) :
    ((pullback a).obj M).VanishesAt (sectionsPullback a M s) x ↔ M.VanishesAt s (a.base x) := by
  obtain ⟨g, rfl⟩ : ∃ g : Γ(Y, ⊤), g • t = s := by
    obtain ⟨g, hg⟩ := (sectionsEquivOfIso (asIso (homOfSectionTop M t)) ⊤).surjective s
    exact ⟨g, by rw [← hg]; exact homOfSectionTop_app_top M t g⟩
  have ht' : IsIso (homOfSectionTop ((pullback a).obj M) (sectionsPullback a M t)) := by
    rw [← map_homOfSectionTop]; infer_instance
  rw [sectionsPullback_smul, vanishesAt_smul_iff_notMem_basicOpen ht',
    vanishesAt_smul_iff_notMem_basicOpen ht, not_iff_not, ← Scheme.preimage_basicOpen_top]
  rfl

/-- **Vanishing of a section of a line bundle is compatible with pullback**: a global section
`s` of an invertible sheaf of modules `L` on `Y` vanishes at `a x` exactly when its pullback
along `a : X ⟶ Y` vanishes at `x`. -/
theorem vanishesAt_sectionsPullback_iff {L : Y.Modules} (hL : L.Invertible) (a : X ⟶ Y)
    (s : Γ(L, ⊤)) (x : X) :
    ((pullback a).obj L).VanishesAt (sectionsPullback a L s) x ↔ L.VanishesAt s (a.base x) := by
  obtain ⟨W, hW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom (a.base x)
  have hmi : IsIso (unitSmulRestrictHom m) := hm
  set e : W.toScheme.structureModules ≅ (pullback W.ι).obj L :=
    asIso (unitSmulRestrictHom m) ≪≫ (restrictFunctorIsoPullback W.ι).app L with he
  set t : Γ((pullback W.ι).obj L, ⊤) := Hom.app e.hom ⊤ (oneSection W.toScheme ⊤) with hte
  have ht : IsIso (homOfSectionTop ((pullback W.ι).obj L) t) := by
    have heq : homOfSectionTop ((pullback W.ι).obj L) t = e.hom := by
      rw [hte, ← unitHomEquivTop_apply, ← unitHomEquivTop_symm_apply,
        Equiv.symm_apply_apply]
    rw [heq]
    infer_instance
  set V : X.Opens := a ⁻¹ᵁ W with hV
  have hxV : x ∈ V := hW
  set x' : V.toScheme := ⟨x, hxV⟩ with hx'
  have hu : (a ∣_ W) ≫ W.ι = V.ι ≫ a := morphismRestrict_ι a W
  -- step 1: restrict to the open subscheme `V` of `X`
  rw [← vanishesAt_sectionsPullback_iff_of_isOpenImmersion V.ι _ _ x']
  -- step 2: identify the two-step pullback along `V.ι ≫ a`
  rw [← pullbackTriangle_hom_app_sectionsPullback (rfl : V.ι ≫ a = V.ι ≫ a) L s,
    vanishesAt_iff_of_iso ((pullbackTriangle (rfl : V.ι ≫ a = V.ι ≫ a)).app L)]
  -- step 3: identify it with the two-step pullback along `(a ∣_ W) ≫ W.ι`
  rw [← pullbackTriangle_hom_app_sectionsPullback hu L s,
    vanishesAt_iff_of_iso ((pullbackTriangle hu).app L),
    vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop (a ∣_ W) ht,
    vanishesAt_sectionsPullback_iff_of_isOpenImmersion W.ι L s]
  congr 2
  exact congrArg (fun f : V.toScheme ⟶ Y ↦ f.base x') hu

end AlgebraicGeometry.Scheme.Modules
