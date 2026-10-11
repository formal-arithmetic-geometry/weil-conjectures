/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteFamily

/-!
# Finite refinements of finite presentation

If a finite morphism `r : T ⟶ X` factors Zariski locally through a morphism `u : U ⟶ X` locally of
finite presentation, so does a finite morphism `r' : T' ⟶ X` of finite presentation whose image
contains that of `r`: write `T` as a limit of finite `X`-schemes of finite presentation
(Stacks 09YZ), and descend the finitely many opens and local factorizations to a finite stage
(Stacks 01Z4, 01ZC).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {T U X : Scheme.{u}}

/-- **Finite refinements can be taken of finite presentation.** If a finite `r : T ⟶ X` factors
through `u` Zariski locally on `T`, with `u` locally of finite presentation and `X` quasi-compact
and quasi-separated, then some finite `r' : T' ⟶ X` of finite presentation, with image containing
that of `r`, factors through `u` Zariski locally on `T'`. -/
theorem Scheme.Hom.exists_locallyOfFinitePresentation_locallyFactorsThrough (r : T ⟶ X)
    [IsFinite r] (u : U ⟶ X) [LocallyOfFinitePresentation u] [CompactSpace X]
    [QuasiSeparatedSpace X] (hr : r.LocallyFactorsThrough u) :
    ∃ (T' : Scheme.{u}) (r' : T' ⟶ X), IsFinite r' ∧ LocallyOfFinitePresentation r' ∧
      Set.range r.base ⊆ Set.range r'.base ∧ r'.LocallyFactorsThrough u := by
  classical
  obtain ⟨F, hF⟩ := r.exists_finiteApproximation_of_isIntegralHom
  have hc := F.isLimit
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace r
  -- affine opens of `T` with factorizations through `u`, finitely many covering `T`
  have hloc (t : T) : ∃ (W : T.Opens) (_ : IsAffineOpen W) (_ : t ∈ W) (φ : W.toScheme ⟶ U),
      φ ≫ u = W.ι ≫ r := by
    obtain ⟨O, htO, φ, hφ⟩ := hr t
    obtain ⟨W, hW, htW, hWO⟩ := exists_isAffineOpen_mem_and_subset htO
    exact ⟨W, hW, htW, T.homOfLE hWO ≫ φ, by
      rw [Category.assoc, hφ, Scheme.homOfLE_ι_assoc]⟩
  choose W hW htW φ hφ using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t ↦ (W t : Set T))
    (fun t ↦ (W t).2) fun t _ ↦ Set.mem_iUnion.2 ⟨t, htW t⟩
  -- each factorization descends to a finite stage
  have hdesc (t : T) : ∃ (j : F.I) (V : (F.D.obj j).Opens) (g : V.toScheme ⟶ U),
      F.π.app j ⁻¹ᵁ V = W t ∧ g ≫ u = V.ι ≫ F.p j := by
    obtain ⟨i, V₀, hV₀, hV₀W⟩ := exists_preimage_eq F.D _ hc (W t) (hW t).isCompact
    have (j : Over i) : CompactSpace ((opensDiagram F.D i V₀).obj j) :=
      isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ V₀.2 hV₀)
    have (j : Over i) : QuasiSeparatedSpace ((opensDiagram F.D i V₀).obj j) :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (F.D.map _ ⁻¹ᵁ _).2).mp
        (.of_quasiSeparatedSpace _)
    let t' : opensDiagram F.D i V₀ ⟶ (Functor.const (Over i)).obj X :=
      { app j := (F.D.map j.hom ⁻¹ᵁ V₀).ι ≫ F.p j.left
        naturality j k f := by
          simp only [opensDiagram_map, Functor.const_obj_obj,
            Functor.const_obj_map, Category.comp_id]
          rw [Scheme.Hom.resLE_comp_ι_assoc, F.map_p] }
    let a : (opensCone F.D (Cone.mk T F.π) i V₀).pt ⟶ U := T.homOfLE hV₀W.le ≫ φ t
    have ha : (opensCone F.D (Cone.mk T F.π) i V₀).π ≫ t' =
        (Functor.const _).map (a ≫ u) := by
      refine NatTrans.ext (funext fun k ↦ ?_)
      simp only [NatTrans.comp_app, opensCone_π_app, Functor.const_obj_obj,
        Functor.const_map_app, t', a, Category.assoc, hφ]
      rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.homOfLE_ι_assoc]
      exact congrArg _ (F.π_p k.left)
    obtain ⟨j', g', -, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (opensDiagram F.D i V₀) t' u _ (isLimitOpensCone F.D _ hc i V₀) a ha
    refine ⟨j'.left, F.D.map j'.hom ⁻¹ᵁ V₀, g', ?_, hg'⟩
    rw [← Scheme.Hom.comp_preimage, (Cone.mk T F.π).w j'.hom, hV₀W]
  choose j V g hVW hg using hdesc
  -- a common stage, at which the descended opens cover
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.inf_objs_exists (s.image j)
  have m₀ (t : s) : k₀ ⟶ j t := (hk₀ (Finset.mem_image_of_mem j t.2)).some
  have hmem (t : s) (x : T) : F.π.app k₀ x ∈ F.D.map (m₀ t) ⁻¹ᵁ V t ↔ x ∈ W t := by
    rw [← hVW t, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      (Cone.mk T F.π).w (m₀ t)]
    rfl
  let O₀ : (F.D.obj k₀).Opens := ⨆ t : s, F.D.map (m₀ t) ⁻¹ᵁ V t
  have hO₀ : F.π.app k₀ ⁻¹ᵁ O₀ = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, ht⟩, (hmem ⟨t, ht⟩ x).2 hxt⟩
  obtain ⟨k, mk, hk⟩ := exists_map_eq_top F.D _ hc O₀ hO₀
  refine ⟨F.D.obj k, F.p k, inferInstance, hF k, ?_, fun x ↦ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨F.π.app k x, by rw [← Scheme.Hom.comp_apply, F.π_p]; rfl⟩
  · have hx : x ∈ F.D.map mk ⁻¹ᵁ O₀ := hk ▸ trivial
    obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨F.D.map (mk ≫ m₀ t) ⁻¹ᵁ V t, ?_, (F.D.map (mk ≫ m₀ t)).resLE _ _ le_rfl ≫ g t, ?_⟩
    · rwa [F.D.map_comp, Scheme.Hom.comp_preimage]
    · rw [Category.assoc, hg, Scheme.Hom.resLE_comp_ι_assoc, F.map_p]

end AlgebraicGeometry
