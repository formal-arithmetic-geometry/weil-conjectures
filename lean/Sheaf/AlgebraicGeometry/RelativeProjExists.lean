/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjData
import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction

/-! # Existence and affine compatibility of relative Proj

Source: blueprint, Nagata compactification, sketch data, order 13;
Stacks Project, Constructions, Tags 01LH, 01NO, 01NP, 01NQ
(blueprint: lemma-nagata-relative-proj-exists).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

private noncomputable def chartFunctor {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    X.affineOpens ⥤ Scheme.{u} where
  obj := A.localProj
  map f := A.localTransition (leOfHom f)
  map_id := A.localTransition_id
  map_comp f g := A.localTransition_comp (leOfHom f) (leOfHom g)

private noncomputable def chartGluing {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    Scheme.Cover.RelativeGluingData X.directedAffineCover where
  functor := chartFunctor A
  natTrans :=
    { app := A.localBase
      naturality _ _ f := (A.localTransition_isPullback (leOfHom f)).w }
  equifibered _ _ f := A.localTransition_isPullback (leOfHom f)

private instance chartFunctor_locallyDirected {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    (chartFunctor A ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs (((chartGluing A).functor ⋙ Scheme.forget).IsLocallyDirected)

private instance chartFunctor_hasColimit {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    HasColimit (chartFunctor A) :=
  inferInstanceAs (HasColimit (chartGluing A).functor)

private noncomputable def chartIso {X : Scheme.{u}} (A : RelativeProjAlgebra X)
    (V : X.affineOpens) :
    A.localProj V ≅ ((chartGluing A).toBase ⁻¹ᵁ V.1).toScheme := by
  let d := chartGluing A
  apply IsOpenImmersion.isoOfRangeEq (colimit.ι d.functor V)
    (d.toBase ⁻¹ᵁ V.1).ι
  rw [Scheme.Opens.range_ι]
  exact congrArg (fun U : d.glued.Opens ↦ (U : Set d.glued))
    ((d.toBase_preimage_eq_opensRange_ι V).symm.trans (by
      change d.toBase ⁻¹ᵁ V.1.ι.opensRange = d.toBase ⁻¹ᵁ V.1
      rw [Scheme.Opens.opensRange_ι]))

private lemma chartIso_hom_ι {X : Scheme.{u}} (A : RelativeProjAlgebra X)
    (V : X.affineOpens) :
    (chartIso A V).hom ≫ ((chartGluing A).toBase ⁻¹ᵁ V.1).ι =
      colimit.ι (chartFunctor A) V := by
  unfold chartIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def construction {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    RelativeProjData A where
  gluing := chartGluing A
  localIso _ := Iso.refl _
  local_over _ := by simp [chartGluing]
  local_transition _ _ _ := by simp [chartGluing, chartFunctor]
  restrictionIso V := (chartIso A V).symm
  restriction_ι V := by
    change (chartIso A V).inv ≫ colimit.ι (chartFunctor A) V = _
    rw [← chartIso_hom_ι A V, Iso.inv_hom_id_assoc]
  restriction_over V := by
    change (chartIso A V).inv ≫ A.localBase V ≫ V.1.ι = _
    have hv : colimit.ι (chartFunctor A) V ≫ (chartGluing A).toBase =
        A.localBase V ≫ V.1.ι := (chartGluing A).ι_toBase V
    rw [← hv, ← chartIso_hom_ι A V]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  restriction_compatibility V W h := by
    apply (cancel_mono (chartIso A V).hom).mp
    apply (cancel_mono ((chartGluing A).toBase ⁻¹ᵁ V.1).ι).mp
    simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [Scheme.homOfLE_ι]
    rw [← Category.assoc, chartIso_hom_ι, Category.assoc, chartIso_hom_ι]
    exact (colimit.w (chartFunctor A) (homOfLE h)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Relative Proj exists with all its affine restriction identifications, and is unique
up to the unique isomorphism respecting those identifications and the structural maps.
The fields of `RelativeProjData` give the restriction isomorphisms, their compatibility
with the canonical section-restriction maps, and their compatibility over the base.
The comparison ranges over any scheme with such compatible affine identifications,
including a realization obtained by gluing a different affine cover.

Source: blueprint, Nagata compactification, sketch data, order 13; Stacks Project,
Constructions, Tags 01LH and 01NQ (blueprint: lemma-nagata-relative-proj-exists).

Proof: (1) For every affine open U use Proj of the graded section ring. The canonical
restriction morphisms identify the model on V with the inverse image of V in the
model on U, by `lem-nagata-proj-affine-restriction` (Tags 01NO and 01NP).
(2) Its identity and composition laws give an equifibered diagram on all affine opens.
Apply `lem-weil-pbc-relative-glueing-affine-opens` to obtain the scheme and structural
map, with all affine restriction isomorphisms and their compatibility equations.
(3) The transition composition law gives iterated affine restriction compatibility.
For arbitrary open restrictions, check equality on affine refinements using
`lem-weil-pbc-affine-opens-basis` and `lem-weil-pbc-scheme-morphism-gluing`.
(4) Given another realization P, on each affine inverse image compare the two charts
via the common local Proj model. On an overlap these comparisons agree on all affine
refinements, by the transition equations. The affine basis and morphism gluing yield
a unique global comparison over X. Reverse the local comparisons to construct its
inverse; both composites are identities by the uniqueness part of morphism gluing.
Any chart-preserving comparison has the same local maps and hence is this one.
(5) A realization from any chosen affine cover has the same identifications after
passing to common affine refinements. Glue the comparisons there as in (4).
Comparisons for three covers agree on common affine refinements, hence globally;
restricting gives compatibility with further restriction. No overlap is assumed affine. -/
theorem exists_relativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) :
    ∃ D : RelativeProjData A,
      ∀ (P : Scheme.{u}) (π : P ⟶ X)
        (i : ∀ V : X.affineOpens, (π ⁻¹ᵁ V.1).toScheme ≅ A.localProj V),
        (∀ V : X.affineOpens,
          (i V).hom ≫ A.localBase V ≫ V.1.ι = (π ⁻¹ᵁ V.1).ι ≫ π) →
        (∀ (V W : X.affineOpens) (h : W ≤ V),
          (i W).inv ≫ P.homOfLE (π.preimage_mono h) ≫ (i V).hom =
            A.localTransition h) →
        ∃! e : D.proj ≅ P,
          e.hom ≫ π = D.π ∧
            ∀ V : X.affineOpens,
              (D.restrictionIso V).inv ≫ (D.π ⁻¹ᵁ V.1).ι ≫ e.hom =
                (i V).inv ≫ (π ⁻¹ᵁ V.1).ι := by
  classical
  let D := construction A
  refine ⟨D, ?_⟩
  intro P π i hi ht
  let 𝒰 : P.OpenCover := X.directedAffineCover.pullback₁ π
  let k : ∀ V : X.affineOpens, A.localProj V ≅ 𝒰.X V :=
    fun V ↦ (i V).symm ≪≫ (pullbackRestrictIsoRestrict π V.1).symm
  have hk (V : X.affineOpens) :
      (k V).hom ≫ 𝒰.f V = (i V).inv ≫ (π ⁻¹ᵁ V.1).ι := by
    dsimp only [k, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc]
    congr 1
    exact pullbackRestrictIsoRestrict_inv_fst π V.1
  have ht' {V W : X.affineOpens} (h : W ≤ V) :
      A.localTransition h ≫ (i V).inv ≫ (π ⁻¹ᵁ V.1).ι =
        (i W).inv ≫ (π ⁻¹ᵁ W.1).ι := by
    rw [← ht V W h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  let e : chartFunctor A ≅ 𝒰.functorOfLocallyDirected :=
    NatIso.ofComponents k (by
      intro W V h
      apply (cancel_mono (𝒰.f V)).mp
      simp only [Category.assoc, Scheme.Cover.functorOfLocallyDirected_map,
        Scheme.Cover.trans_map, hk]
      exact ht' (leOfHom h))
  let c := (Cocone.precompose e.hom).obj 𝒰.coconeOfLocallyDirected
  let hc : IsColimit c :=
    (IsColimit.precomposeHomEquiv e 𝒰.coconeOfLocallyDirected).symm
      (Scheme.OpenCover.isColimitCoconeOfLocallyDirected 𝒰)
  let z : D.proj ≅ P := (colimit.isColimit (chartFunctor A)).coconePointUniqueUpToIso hc
  have hz (V : X.affineOpens) :
      colimit.ι (chartFunctor A) V ≫ z.hom = (i V).inv ≫ (π ⁻¹ᵁ V.1).ι := by
    exact ((colimit.isColimit (chartFunctor A)).comp_coconePointUniqueUpToIso_hom hc V).trans
      (hk V)
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · apply colimit.hom_ext
    intro V
    change colimit.ι (chartFunctor A) V ≫ z.hom ≫ π =
      colimit.ι (chartFunctor A) V ≫ (chartGluing A).toBase
    rw [reassoc_of% (hz V)]
    have hv : colimit.ι (chartFunctor A) V ≫ (chartGluing A).toBase =
        A.localBase V ≫ V.1.ι := (chartGluing A).ι_toBase V
    rw [hv]
    rw [← hi V]
    simp
  · intro V
    change (chartIso A V).hom ≫ ((chartGluing A).toBase ⁻¹ᵁ V.1).ι ≫ z.hom = _
    rw [← Category.assoc, chartIso_hom_ι, hz]
  · intro z' hz'
    apply Iso.ext
    apply colimit.hom_ext
    intro V
    change colimit.ι (chartFunctor A) V ≫ z'.hom =
      colimit.ι (chartFunctor A) V ≫ z.hom
    rw [hz V]
    have hh := hz'.2 V
    change (chartIso A V).hom ≫ ((chartGluing A).toBase ⁻¹ᵁ V.1).ι ≫ z'.hom = _ at hh
    rwa [← Category.assoc, chartIso_hom_ι] at hh

end AlgebraicGeometry
