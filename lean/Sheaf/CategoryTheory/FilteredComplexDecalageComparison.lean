/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor
import Sheaf.CategoryTheory.FilteredComplexDecalagePageCoherence
import all Sheaf.CategoryTheory.FilteredComplexCanonicalModel

/-! # Decalage and the canonical quotient sequence

Source: Stacks Project, Tags 012K and 015X.
(blueprint: lem-sp-filtered-complex-decalage-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def decalagePageComplexIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : FilteredObject (CochainComplex C ℤ)) (r : ℤ) (hr : 2 ≤ r) :
    ((filteredComplexCanonicalModel C).S.obj U).page r hr ≅
      (((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
        r hr :=
  HomologicalComplex.Hom.isoOfComponents
    (fun pq ↦ filteredComplexDecalagePageIso U pq.1 pq.2 r hr)
    (fun i j _ ↦ (filteredComplex_decalage_page_coherence U).differential r hr i j)

private noncomputable def decalageSequenceHom
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : FilteredObject (CochainComplex C ℤ)) :
    (filteredComplexCanonicalModel C).S.obj U ⟶
      ((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence where
  hom r hr := (decalagePageComplexIso U r hr).hom
  comm r r' pq hrr' hr := by
    subst r'
    exact (filteredComplex_decalage_page_coherence U).successor r hr _ (fun _ ↦ rfl) pq

private noncomputable def decalageSequenceIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : FilteredObject (CochainComplex C ℤ)) :
    (filteredComplexCanonicalModel C).S.obj U ≅
      ((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence where
  hom := decalageSequenceHom U
  inv :=
    { hom r hr := (decalagePageComplexIso U r hr).inv
      comm r r' pq hrr' hr := by
        have hh := (decalageSequenceHom U).comm r r' pq hrr' hr
        change HomologicalComplex.homologyMap (decalagePageComplexIso U r hr).hom pq ≫ _ =
          _ ≫ (decalagePageComplexIso U r' (by omega)).hom.f pq at hh
        apply (cancel_epi
          (HomologicalComplex.homologyMap (decalagePageComplexIso U r hr).hom pq)).1
        rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp]
        rw [Iso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp]
        rw [← Category.assoc, hh]
        simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
          HomologicalComplex.id_f, Category.comp_id] }
  hom_inv_id := by
    apply SpectralSequence.hom_ext
    intro r hr
    exact (decalagePageComplexIso U r hr).hom_inv_id
  inv_hom_id := by
    apply SpectralSequence.hom_ext
    intro r hr
    exact (decalagePageComplexIso U r hr).inv_hom_id


private theorem decalagePage_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (p q r : ℤ) (hr : 2 ≤ r) :
    (((filteredComplexCanonicalModel C).S.map t).hom r hr).f (p, q) ≫
        (filteredComplexDecalagePageIso V p q r hr).hom ≫
        filteredComplexDecalagePageEmbedding V p q r hr =
      (filteredComplexDecalagePageIso U p q r hr).hom ≫
        filteredComplexDecalagePageEmbedding U p q r hr ≫
        HomologicalComplex.homologyMap
          (DecreasingFiltration.decalageTowerIntervalMap t (q : EInt)
            ((q + (r - 1) : ℤ) : EInt) (by simp; omega)).τ₃ (p + q) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.defeqAttrib.useBackward true in
      let S := quotientPageSquares t r
      obtain ⟨ρ, hρ⟩ := representative_map t S.s S.hs p (p + q) r
      obtain ⟨zU, _, hzUepi, _, hzU, _⟩ :=
        U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
      obtain ⟨zV, _, _, _, hzV, _⟩ :=
        V.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
      have : Epi zU := hzUepi
      have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
        unfold filteredComplexPageπ
        infer_instance
      have hzρ : zU ≫ S.kz (p, q) = ρ ≫ zV := by
        apply (cancel_mono (V.filtration.complexCycles p (p + q) r).arrow).1
        rw [Category.assoc, S.hkz, ← Category.assoc, hzU, Category.assoc]
        have hg := congrArg (fun f ↦ f.f (p + q)) (S.hg p)
        simp only [HomologicalComplex.comp_f] at hg
        rw [hg, ← Category.assoc, ← hρ, Category.assoc, ← hzV, ← Category.assoc]
      have hρambient : ρ ≫ (V.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
            (V.filtration.step p).arrow.f (p + q) =
          (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
            (U.filtration.step p).arrow.f (p + q) ≫ t.hom.f (p + q) := by
        rw [← Category.assoc, hρ, Category.assoc]
        exact congrArg (fun f ↦
          (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫ f)
          (congrArg (fun f ↦ f.f (p + q)) (S.hs p))
      have hmap := filteredComplexCanonicalMap_property t p q r (by omega)
        S.s (S.g p) (S.kz (p, q)) (S.k (p, q)) S.hs (S.hg p) (S.hkz (p, q)) (S.hk (p, q))
      have hU := filteredComplexDecalagePageIso_property U p q r hr zU hzU
      have hV := filteredComplexDecalagePageIso_property V p q r hr zV hzV
      apply (cancel_epi (zU ≫ filteredComplexPageπ U.obj U.filtration r (p, q))).1
      change (zU ≫ filteredComplexPageπ U.obj U.filtration r (p, q)) ≫
          (((filteredComplexCanonicalMap t).hom r (by omega)).f (p, q) ≫ _) = _
      rw [hmap]
      change (zU ≫ filteredComplexPageπ U.obj U.filtration r (p, q)) ≫
          (S.k (p, q) ≫ (filteredComplexDecalagePageIso V p q r hr).hom ≫
            filteredComplexDecalagePageEmbedding V p q r hr) =
        (zU ≫ filteredComplexPageπ U.obj U.filtration r (p, q)) ≫
          ((filteredComplexDecalagePageIso U p q r hr).hom ≫
            filteredComplexDecalagePageEmbedding U p q r hr ≫
            HomologicalComplex.homologyMap
              (DecreasingFiltration.decalageTowerIntervalMap t (q : EInt)
                ((q + (r - 1) : ℤ) : EInt) (by simp; omega)).τ₃ (p + q))
      simp only [Category.assoc]
      rw [reassoc_of% (S.hk (p, q))]
      rw [← Category.assoc, hzρ]
      simp only [Category.assoc]
      rw [hV, reassoc_of% hU]
      simpa only [Category.assoc] using
        filteredComplexDecalageRepresentativeClass_naturality t p q r hr ρ hρambient

/-- The canonical sequence of a filtered complex is the sequence of the mapping-cone
spectral object of its decalage tower, naturally on the first page.
Source: Stacks Project, Tag 012K (cycle and boundary quotients) and Tag 015X,
Remark 13.26.15 (second filtration).
(blueprint: lem-sp-filtered-complex-decalage-comparison).

Proof. Write D for the decalage of F. Its tower at the integer q is D^(1-q).
The mapping cone of D^(1-a) -> D^(1-b), for a <= b, is quasi-isomorphic to its
cokernel, since the step inclusion is monic. Thus interval cohomology is the
cohomology of D^(1-b)/D^(1-a), compatibly with inclusions and connecting maps.
Substitute D^a K^n = F^(a+n) K^n intersect d^-1(F^(a+n+1) K^(n+1)).
Write Z_s(F)^(p,n) = F^p K^n intersect d^-1(F^(p+s) K^(n+1)). Its page
denominator is Z_(s-1)(F)^(p+1,n) plus d Z_(s-1)(F)^(p-s+1,n-1).
For a=p-n and r>=2, substitution and d squared equal to zero identify
Z_(r-1)(D)^(a,n) with Z_r(F)^(p,n), and identify their two denominator
terms respectively. Thus E_(r-1)(D)^(a,n-a) is E_r(F)^(p,n-p).
The spectral-object r-page is this (r-1)-page of D, with a=-q and n=p+q.
Its differential changes (a,n) to (a+r-1,n+1), hence (p,q) to
(p+r,q+1-r), as required. The identification sends a
representative to its own class; its differential is therefore represented
by the same differential of K. The next-page homology isomorphism sends a
successor cycle to its quotient class on both sides. Cancel the epimorphisms
from representative objects to prove these two compatibilities and assemble
the isomorphism of sequences. For a filtered map, its chain-map equation
preserves these representatives. Cancel the same epimorphisms to obtain the
page-two square. Infinite endpoints are zero and K by construction and do
not occur in these finite-page calculations. No boundedness assumption enters. -/
theorem filteredComplex_decalage_comparison
    (C : Type u) [Category.{v} C] [Abelian C] :
    ∃ e : ∀ U : FilteredObject (CochainComplex C ℤ),
      (filteredComplexCanonicalModel C).S.obj U ≅
        ((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence,
      ∀ {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (p q : ℤ),
        (((filteredComplexCanonicalModel C).S.map t).hom 2).f (p, q) ≫
            (Abelian.SpectralObject.pageTwoComparison
              ((filteredComplexDecalageSpectralObjectFunctor C).obj V)
              (e V) p q (p + q) rfl).hom =
          (Abelian.SpectralObject.pageTwoComparison
            ((filteredComplexDecalageSpectralObjectFunctor C).obj U)
            (e U) p q (p + q) rfl).hom ≫
            (((filteredComplexDecalageSpectralObjectFunctor C).map t).hom (p + q)).app
              (ComposableArrows.mk₁
                (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.defeqAttrib.useBackward true in
      refine ⟨decalageSequenceIso, ?_⟩
      intro U V t p q
      have hh := decalagePage_naturality t p q 2 le_rfl
      rw [filteredComplexDecalagePageEmbedding_two, filteredComplexDecalagePageEmbedding_two]
        at hh
      apply (cancel_mono
        (filteredComplexDecalageIntervalIso V (q : EInt) ((q + (2 - 1) : ℤ) : EInt)
          (by simp) (p + q)).hom).1
      have hcomp (W : FilteredObject (CochainComplex C ℤ)) :
          (Abelian.SpectralObject.pageTwoComparison
            ((filteredComplexDecalageSpectralObjectFunctor C).obj W)
            (decalageSequenceIso W) p q (p + q) rfl).hom =
          (filteredComplexDecalagePageIso W p q 2 le_rfl).hom ≫
            (((filteredComplexDecalageSpectralObjectFunctor C).obj W).spectralSequenceFirstPageXIso
              Abelian.SpectralObject.coreE₂Cohomological (p, q) (q : EInt)
              ((q + (2 - 1) : ℤ) : EInt) rfl rfl (p + q) rfl).hom := by
        rfl
      rw [hcomp U, hcomp V]
      simp only [Category.assoc]
      erw [filteredComplexDecalageIntervalIso_naturality]
      dsimp only [HomologicalComplex.homologyFunctor] at *
      simp only [Category.assoc] at hh
      exact hh

end CategoryTheory
