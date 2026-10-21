/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Sheaf.CategoryTheory.LargeSetSheafification

/-!
# Finite coefficient descent on quasi-compact pro-étale objects

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-sections;
Stacks Project, Sites, Tag 0738 (blueprint: det-lem-coefficient-finite-descent-sections).

The three statements give clause (1) for sets and abelian groups and clause (2)
for the existing finite-subextension coefficient sheaves. No quasi-separatedness
is imposed in the injective-transition case or in coefficient descent.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

-- For an affine target, the finite affine refinement remains an fpqc covering:
-- every arrow has affine source and target and is therefore quasi-compact.
private theorem finite_affine_cover_of_affine {X : Scheme.{u}} {W : X.ProEt}
    [IsAffine W.left] {R : Sieve W} (hR : R ∈ Scheme.ProEt.topology X W) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (U : ι → X.ProEt) (g : ∀ i, U i ⟶ W),
      (∀ i, R (g i)) ∧ (∀ i, IsAffine (U i).left) ∧
        Sieve.ofArrows U g ∈ Scheme.ProEt.topology X W := by
  classical
  obtain ⟨P, hP, hle⟩ := Scheme.ProEt.mem_topology_iff.mp hR
  obtain ⟨κ, Y, f, rfl⟩ := P.exists_eq_ofArrows
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
  let C : W.left.Cover (Scheme.precoverage @WeaklyEtale) :=
    ⟨⟨κ, fun i ↦ (Y i).left, fun i ↦ (f i).left⟩, hP.2⟩
  have : QuasiCompactCover C.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hP.1
  obtain ⟨D, a, hD, -⟩ := QuasiCompactCover.exists_hom.{u + 1, u} C
  let _ := hD
  have (i : D.I₀) : WeaklyEtale (D.f i) := D.map_prop i
  have : WeaklyEtale W.hom := W.prop
  let U (i : D.I₀) : X.ProEt := Scheme.ProEt.mk (D.f i ≫ W.hom)
  let g (i : D.I₀) : U i ⟶ W := MorphismProperty.Over.homMk (D.f i)
  refine ⟨D.I₀, hD, U, g, ?_, fun i ↦ inferInstanceAs (IsAffine (Scheme.Spec.obj (op (D.X i)))), ?_⟩
  · intro i
    let b : U i ⟶ Y (a.s₀ i) := MorphismProperty.Over.homMk (a.h₀ i) (by
      change a.h₀ i ≫ (Y (a.s₀ i)).hom = D.f i ≫ W.hom
      rw [← MorphismProperty.Over.w (f (a.s₀ i)), ← Category.assoc, a.w₀ i]
      rfl)
    have hb : b ≫ f (a.s₀ i) = g i := by
      apply MorphismProperty.Over.Hom.ext
      exact a.w₀ i
    rw [← hb]
    exact R.downward_closed (hle _ _ (.mk (a.s₀ i))) b
  · apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact D.cover.ofQuasiCompactCover.mem₀

private theorem finite_affine_cover {X : Scheme.{u}} {W : X.ProEt}
    [CompactSpace W.left] {R : Sieve W} (hR : R ∈ Scheme.ProEt.topology X W) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (U : ι → X.ProEt) (g : ∀ i, U i ⟶ W),
      (∀ i, R (g i)) ∧ (∀ i, IsAffine (U i).left) ∧
        Sieve.ofArrows U g ∈ Scheme.ProEt.topology X W := by
  classical
  let O := W.left.affineCover.finiteSubcover
  let Z (i : O.I₀) := Scheme.ProEt.ofOpenImmersion W (O.f i)
  let z (i : O.I₀) : Z i ⟶ W := Scheme.ProEt.ofOpenImmersionHom W (O.f i)
  have (i : O.I₀) : IsAffine (Z i).left := by
    change IsAffine (W.left.affineCover.X _)
    infer_instance
  have hz : Sieve.ofArrows Z z ∈ Scheme.ProEt.topology X W := by
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (O.f)
    · intro x
      exact ⟨O.idx x, O.covers x⟩
    · intro i
      exact Sieve.ofArrows_mk _ _ i
  have hlocal (i : O.I₀) := finite_affine_cover_of_affine
    ((Scheme.ProEt.topology X).pullback_stable (z i) hR)
  choose κ hκ U g hRg hU hg using hlocal
  let (i : O.I₀) := hκ i
  refine ⟨Σ i, κ i, inferInstance, fun p ↦ U p.1 p.2,
    fun p ↦ g p.1 p.2 ≫ z p.1, fun p ↦ hRg p.1 p.2,
    fun p ↦ hU p.1 p.2, ?_⟩
  have hb := (Scheme.ProEt.topology X).bindOfArrows hz hg
  simpa only [Presieve.bindOfArrows_ofArrows] using hb


private theorem finite_common_stage {I : Type v} [SmallCategory I] [IsFiltered I]
    {ι : Type*} [Finite ι] (k : ι → I) :
    ∃ j : I, Nonempty (∀ i, k i ⟶ j) := by
  classical
  let _ := Fintype.ofFinite ι
  let O : Finset I := Finset.univ.image k
  exact ⟨IsFiltered.sup O ∅, ⟨fun i ↦ IsFiltered.toSup O ∅
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩⟩

private theorem finite_common_arrow {I : Type v} [SmallCategory I] [IsFiltered I]
    {k : I} {ι : Type*} [Finite ι] {j : ι → I} (a : ∀ i, k ⟶ j i) :
    ∃ (k' : I) (A : k ⟶ k') (b : ∀ i, j i ⟶ k'), ∀ i, a i ≫ b i = A := by
  classical
  let _ := Fintype.ofFinite ι
  let O : Finset I := insert k (Finset.univ.image j)
  have hk : k ∈ O := Finset.mem_insert_self _ _
  have hj (i : ι) : j i ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let H : Finset (Σ' (X Y : I) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun i ↦ ⟨k, j i, hk, hj i, a i⟩
  exact ⟨IsFiltered.sup O H, IsFiltered.toSup O H hk, fun i ↦ IsFiltered.toSup O H (hj i),
    fun i ↦ IsFiltered.toSup_commutes O H hk (hj i)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

section SetComparison

variable {X : Scheme.{u}} {I : Type v} [SmallCategory I] [IsFiltered I]
  {F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))}
  {c : Cocone F}

omit [IsFiltered I] in
private theorem presheaf_colimit (hc : IsColimit c) :
    ∃ (E : Cocone (F ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) φ ∧
      Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) φ ∧
      ∀ i, E.ι.app i ≫ φ = (c.ι.app i).hom := by
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective (Type (max (u + 1) v)) :=
    largeSetSheafification_locallyBijective _
  let E := colimit.cocone (F ⋙ sheafToPresheaf _ _)
  let hE : IsColimit E := colimit.isColimit _
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  refine ⟨E, hE, toSheafify _ E.pt ≫ e.hom.hom, ?_, ?_, fun i ↦ ?_⟩
  · infer_instance
  · infer_instance
  · rw [← Category.assoc, ← Sheaf.sheafifyCocone_ι_app_val,
      ← ObjectProperty.FullSubcategory.comp_hom,
      IsColimit.comp_coconePointUniqueUpToIso_hom]

omit [IsFiltered I] in
private theorem local_representatives (hc : IsColimit c) {W : X.ProEt}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ Scheme.ProEt.topology X W, ∀ ⦃U : X.ProEt⦄ (f : U ⟶ W), R f →
      ∃ (i : I) (t : (F.obj i).obj.obj (op U)),
        (c.ι.app i).hom.app (op U) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, -, hφ⟩ := presheaf_colimit hc
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun U f ⟨p, hp⟩ ↦ ?_⟩
  have hEU := isColimitOfPreserves ((evaluation _ _).obj (op U)) hE
  obtain ⟨i, t, rfl⟩ := Types.jointly_surjective_of_isColimit hEU p
  refine ⟨i, t, Eq.trans ?_ hp⟩
  change (c.ι.app i).hom.app _ t = (E.ι.app i ≫ φ).app _ t
  rw [hφ]
  rfl

private theorem local_equality (hc : IsColimit c) {W : X.ProEt} {i : I}
    (s t : (F.obj i).obj.obj (op W))
    (h : (c.ι.app i).hom.app (op W) s = (c.ι.app i).hom.app (op W) t) :
    ∃ R ∈ Scheme.ProEt.topology X W, ∀ ⦃U : X.ProEt⦄ (f : U ⟶ W), R f →
      ∃ (j : I) (a : i ⟶ j),
        (F.map a).hom.app (op U) ((F.obj i).obj.map f.op s) =
          (F.map a).hom.app (op U) ((F.obj i).obj.map f.op t) := by
  obtain ⟨E, hE, φ, -, hi, hφ⟩ := presheaf_colimit hc
  have h' : φ.app (op W) ((E.ι.app i).app (op W) s) =
      φ.app (op W) ((E.ι.app i).app (op W) t) := by
    change (E.ι.app i ≫ φ).app _ s = (E.ι.app i ≫ φ).app _ t
    rw [hφ]
    exact h
  refine ⟨_, Presheaf.equalizerSieve_mem _ φ _ _ h', fun U f hf ↦ ?_⟩
  have hEU := isColimitOfPreserves ((evaluation _ _).obj (op U)) hE
  apply (Types.FilteredColimit.isColimit_eq_iff' hEU _ _).mp
  change (E.ι.app i).app _ ((F.obj i).obj.map f.op s) =
    (E.ι.app i).app _ ((F.obj i).obj.map f.op t)
  have hn := (E.ι.app i).naturality f.op
  have e₁ := ConcreteCategory.congr_hom hn s
  have e₂ := ConcreteCategory.congr_hom hn t
  simp only [ConcreteCategory.comp_apply] at e₁ e₂
  erw [e₁, e₂]
  exact hf

private theorem eventual_equality (hc : IsColimit c) {W : X.ProEt} [CompactSpace W.left]
    {i : I} (s t : (F.obj i).obj.obj (op W))
    (h : (c.ι.app i).hom.app (op W) s = (c.ι.app i).hom.app (op W) t) :
    ∃ (j : I) (a : i ⟶ j),
      (F.map a).hom.app (op W) s = (F.map a).hom.app (op W) t := by
  obtain ⟨R, hR, hloc⟩ := local_equality hc s t h
  obtain ⟨κ, hκ, U, g, hRg, -, hcov⟩ := finite_affine_cover hR
  let _ := hκ
  choose j a ha using fun k ↦ hloc (g k) (hRg k)
  obtain ⟨j', A, b, hb⟩ := finite_common_arrow a
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp (F.obj j').property
  refine ⟨j', A, ?_⟩
  apply ((Presieve.isSheafFor_iff_generate _).mpr (hsh _ hcov)).isSeparatedFor.ext
  rintro Z f ⟨k⟩
  change (F.obj j').obj.map (g k).op _ = (F.obj j').obj.map (g k).op _
  have hn (x : (F.obj i).obj.obj (op W)) :
      (F.obj j').obj.map (g k).op ((F.map A).hom.app _ x) =
        (F.map (b k)).hom.app _
          ((F.map (a k)).hom.app _ ((F.obj i).obj.map (g k).op x)) := by
    rw [← hb k, F.map_comp]
    exact (NatTrans.naturality_apply (F.map (a k) ≫ F.map (b k)).hom (g k).op x).symm
  rw [hn, hn, ha k]

private theorem stage_injective
    (hc : IsColimit c)
    (hinj : ∀ (i j : I) (a : i ⟶ j) (U : X.ProEt),
      Function.Injective ((F.map a).hom.app (op U))) (i : I) (W : X.ProEt) :
    Function.Injective ((c.ι.app i).hom.app (op W)) := by
  intro s t h
  obtain ⟨R, hR, hloc⟩ := local_equality hc s t h
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp (F.obj i).property
  apply (hsh _ hR).isSeparatedFor.ext
  intro U f hf
  obtain ⟨j, a, ha⟩ := hloc f hf
  exact hinj i j a U ha


private theorem section_representative (hc : IsColimit c) {W : X.ProEt}
    [CompactSpace W.left]
    (hW : QuasiSeparated (toSpecZ W.left) ∨
      ∀ (i j : I) (a : i ⟶ j) (U : X.ProEt),
        Function.Injective ((F.map a).hom.app (op U)))
    (s : c.pt.obj.obj (op W)) :
    ∃ (i : I) (t : (F.obj i).obj.obj (op W)), (c.ι.app i).hom.app (op W) t = s := by
  classical
  obtain ⟨R, hR, hloc⟩ := local_representatives hc s
  obtain ⟨κ, hκ, U, g, hRg, hU, hcov⟩ := finite_affine_cover hR
  let _ := hκ
  choose i₁ t₁ ht₁ using fun k ↦ hloc (g k) (hRg k)
  obtain ⟨i, ⟨b⟩⟩ := finite_common_stage i₁
  let t₂ (k : κ) : (F.obj i).obj.obj (op (U k)) := (F.map (b k)).hom.app _ (t₁ k)
  have ht₂ (k : κ) : (c.ι.app i).hom.app _ (t₂ k) = c.pt.obj.map (g k).op s := by
    rw [← ht₁ k, ← c.w (b k)]
    rfl
  have hpair (kl : κ × κ) : ∃ (j : I) (a : i ⟶ j),
      (F.map a).hom.app _
          ((F.obj i).obj.map (pullback.fst (g kl.1) (g kl.2)).op (t₂ kl.1)) =
        (F.map a).hom.app _
          ((F.obj i).obj.map (pullback.snd (g kl.1) (g kl.2)).op (t₂ kl.2)) := by
    have he : (c.ι.app i).hom.app _
          ((F.obj i).obj.map (pullback.fst (g kl.1) (g kl.2)).op (t₂ kl.1)) =
        (c.ι.app i).hom.app _
          ((F.obj i).obj.map (pullback.snd (g kl.1) (g kl.2)).op (t₂ kl.2)) := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht₂, ht₂]
      change c.pt.obj.map _ (c.pt.obj.map _ s) = c.pt.obj.map _ (c.pt.obj.map _ s)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, pullback.condition]
    rcases hW with hqs | hinj
    · let : QuasiSeparated (toSpecZ W.left) := hqs
      have : QuasiSeparatedSpace W.left :=
        quasiSeparatedSpace_of_quasiSeparated (toSpecZ W.left)
      have : IsAffine (U kl.1).left := hU _
      have : IsAffine (U kl.2).left := hU _
      let e := PreservesPullback.iso
        (Scheme.ProEt.forget X ⋙ Over.forget X) (g kl.1) (g kl.2)
      have : QuasiCompact (g kl.1).left := quasiCompact_of_compactSpace _
      have : CompactSpace ↥(pullback (C := Scheme.{u}) (g kl.1).left (g kl.2).left) := inferInstance
      have : CompactSpace (pullback (g kl.1) (g kl.2)).left :=
        @Homeomorph.compactSpace _ _ _ _ ‹_›
          (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).symm
      exact eventual_equality hc _ _ he
    · refine ⟨i, 𝟙 i, ?_⟩
      simpa using stage_injective hc hinj i _ he
  choose j a ha using hpair
  obtain ⟨j', A, b', hb'⟩ := finite_common_arrow a
  let t₃ (k : κ) : (F.obj j').obj.obj (op (U k)) := (F.map A).hom.app _ (t₂ k)
  have ht₃ (k : κ) : (c.ι.app j').hom.app _ (t₃ k) = c.pt.obj.map (g k).op s := by
    rw [← ht₂ k, ← c.w A]
    rfl
  have hA (kl : κ × κ) :
      (F.obj j').obj.map (pullback.fst (g kl.1) (g kl.2)).op (t₃ kl.1) =
        (F.obj j').obj.map (pullback.snd (g kl.1) (g kl.2)).op (t₃ kl.2) := by
    have hn (k : κ) (r : pullback (g kl.1) (g kl.2) ⟶ U k) :
        (F.obj j').obj.map r.op (t₃ k) =
          (F.map (b' kl)).hom.app _
            ((F.map (a kl)).hom.app _ ((F.obj i).obj.map r.op (t₂ k))) := by
      change (F.obj j').obj.map r.op ((F.map A).hom.app _ (t₂ k)) = _
      rw [← hb' kl, F.map_comp]
      exact (NatTrans.naturality_apply (F.map (a kl) ≫ F.map (b' kl)).hom r.op (t₂ k)).symm
    rw [hn, hn, ha kl]
  have hsh (G : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))) :
      Presieve.IsSheafFor G.obj (Presieve.ofArrows U g) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp G.property _ hcov)
  obtain ⟨t, ht, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).mp
    (hsh (F.obj j'))) t₃ fun k l ↦ hA (k, l)
  refine ⟨j', t, (hsh c.pt).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨k⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← ht₃ k]
  erw [← ht k]
  exact (NatTrans.naturality_apply (c.ι.app j').hom (g k).op t).symm

end SetComparison

/-- The section-colimit comparison for sets is injective on a quasi-compact object,
and bijective if the object is quasi-separated or all transitions are sectionwise injective.
The sheaf colimit is supplied as an arbitrary cocone `c` with universal property `hc`.
Source: Stacks Project, Sites, Tag 0738(2)--(4), and the corrected blueprint node
(blueprint: det-lem-coefficient-finite-descent-sections), clause (1).

Proof: (1) Form the sectionwise presheaf colimit; sheafification is the sheaf colimit
by its adjunction (lem-weil-pbc-presheaf-colimits-sectionwise,
def-weil-pbc-sheafification). Filteredness gives representatives and eventual equality,
including equalization of parallel arrows (def-weil-pbc-category-colimit).
(2) An fpqc covering of a quasi-compact pro-etale object has a finite affine refinement
(sk-def-pe-site, def-weil-pbc-quasi-compact-scheme, def-weil-pbc-sites-and-cohomology).
(3) Equal images are equal locally by lem-weil-pbc-site-sheafification-sections-local.
On the finite refinement, move the equality witnesses to a common stage and use the
stage sheaf's separatedness. This proves injectivity.
(4) For a quasi-separated object, pairwise overlaps of affine covering objects are
quasi-compact: base change its quasi-compact diagonal to their affine product over Z
(def-weil-quasi-separated-morphism, lem-pc-quasi-compact-base-change,
lem-weil-pbc-fibre-product-affine-spectra). Lift a section locally, refine finitely,
move to a common stage, and use (3) on the finitely many overlaps. A further common
stage makes the representatives compatible, and the sheaf condition glues them.
(5) Alternatively, injective transitions make every stage inject into its presheaf
colimit, using filteredness to equalize parallel arrows. Local equality and the stage
sheaf condition then make every stage inject into the sheaf colimit on every object.
Move local representatives on a finite cover to one stage; they agree on all overlaps
by this injectivity and glue, without assuming quasi-compact overlaps. -/
theorem set_sections_filtered_colimit (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (c : Cocone F) (hc : IsColimit c) :
    Function.Injective
        (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
          (Type (max (u + 1) v))).obj (op V)).mapCocone c)) ∧
      ((QuasiSeparated (toSpecZ V.left) ∨
          ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
            Function.Injective ((F.map f).hom.app (op U))) →
        Function.Bijective
          (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
            (Type (max (u + 1) v))).obj (op V)).mapCocone c))) := by
  let ev := (sheafSections (Scheme.ProEt.topology X)
    (Type (max (u + 1) v))).obj (op V)
  let D := F ⋙ ev
  let d := ev.mapCocone c
  have hι (i : I) (s : (F.obj i).obj.obj (op V)) :
      colimit.desc D d (colimit.ι D i s) = (c.ι.app i).hom.app (op V) s :=
    ConcreteCategory.congr_hom (colimit.ι_desc d i) s
  have hinj : Function.Injective (colimit.desc D d) := by
    intro x y hxy
    obtain ⟨i, s, t, rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit D) x y
    have hst := (hι i s).symm.trans (hxy.trans (hι i t))
    obtain ⟨j, a, ha⟩ := eventual_equality hc s t hst
    exact (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D) s t).mpr
      ⟨j, a, ha⟩
  refine ⟨hinj, fun h ↦ ⟨hinj, ?_⟩⟩
  intro s
  obtain ⟨i, t, ht⟩ := section_representative hc h s
  exact ⟨colimit.ι D i t, (hι i t).trans ht⟩

/-- The same section-colimit comparison for abelian sheaves, with the same two
sufficient conditions for bijectivity. In both comparisons, `c` with `hc` is an
arbitrary chosen sheaf-colimit cocone; the source is the chosen section-group colimit.
Source: Stacks Project, Sites, Tags 0738 and 03CO(4), and blueprint clause (1)
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: Use the set comparison just stated (steps (1)--(5) of this node).
The presheaf colimit is sectionwise (lem-weil-pbc-presheaf-colimits-sectionwise),
and forgetting abelian groups preserves filtered colimits
(lem-weil-pbc-abelian-groups-forget-filtered-colimits).
Abelian sheafification has the underlying set sheafification
(lem-pc-sites-sheafification-underlying-sets), so the underlying comparison is
precisely the set comparison, with unchanged compactness and transition hypotheses.
This also agrees with the abelian sheaf colimit of
lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact. -/
theorem abelian_sections_filtered_colimit (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (c : Cocone F) (hc : IsColimit c) :
    Function.Injective
        (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
          AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapCocone c)) ∧
      ((QuasiSeparated (toSpecZ V.left) ∨
          ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
            Function.Injective ((F.map f).hom.app (op U))) →
        Function.Bijective
          (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
            AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapCocone c))) := by
  let J := Scheme.ProEt.topology X
  let A := AddCommGrpCat.{max (u + 1) v}
  let U := forget A
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} U :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max (u + 1) v,
      u + 1, max (u + 1) v} U
  have : PreservesFilteredColimitsOfSize.{v, v} U :=
    preservesFilteredColimitsOfSize_shrink.{v, max (u + 1) v,
      v, max (u + 1) v} U
  have : J.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification J U
  have : PreservesColimitsOfShape I (sheafCompose J U) := by
    rw [(sheafificationAdjunction J A).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J U (sheafificationAdjunction J A)
        (sheafificationAdjunction J (Type (max (u + 1) v))))
  let D := F ⋙ (sheafSections J A).obj (op V)
  let d := ((sheafSections J A).obj (op V)).mapCocone c
  let d' := ((sheafSections J (Type (max (u + 1) v))).obj (op V)).mapCocone
    ((sheafCompose J U).mapCocone c)
  have hs := set_sections_filtered_colimit X V I (F ⋙ sheafCompose J U)
    ((sheafCompose J U).mapCocone c) (isColimitOfPreserves (sheafCompose J U) hc)
  have he : colimit.post D U ≫ U.map (colimit.desc D d) =
      colimit.desc _ d' := colimit.post_desc D U d
  have hi : Function.Bijective (colimit.post D U) :=
    (isIso_iff_bijective _).mp inferInstance
  have he' : (fun x ↦ colimit.desc _ d' x) =
      (fun x ↦ colimit.desc D d x) ∘ (colimit.post D U) := by
    funext x
    exact (ConcreteCategory.congr_hom he x).symm
  change Function.Injective (fun x ↦ colimit.desc _ d' x) ∧ _ at hs
  rw [he'] at hs
  refine ⟨?_, ?_⟩
  · exact hs.1.of_comp_right hi.2
  · intro h
    have hb := hs.2 h
    have hb' : Function.Bijective
        ((fun x ↦ colimit.desc D d x) ∘ (colimit.post D U)) := by
      rw [← he']
      exact hb
    exact ⟨hb'.1.of_comp_right hi.2, hb'.2.of_comp⟩


private theorem coefficient_section_injective (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (V : X.ProEt) :
    Function.Injective ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) := by
  have : Mono (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E) := by
    apply Sheaf.mono_of_injective
    intro S a b h
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    apply Subtype.val_injective
    exact congrArg (fun z ↦ (z.down : C(S.unop, PadicAlgCl l)) s) h
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  have : Mono (padicSubfieldRingObjToPadicAlgCl X l E) :=
    (upperStarFromPoint X).map_mono _
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- Coefficient inclusions are injective on sections, their ranges cover the algebraic
closure coefficient sections, and every finite set or finite family of finite matrices
has entries in one finite subextension. No quasi-separatedness is required.
Source: blueprint main-20261015, coefficient finite descent, clause (2)
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: (7) On profinite test objects, the condensed coefficient inclusion is injective
because postcomposition with a subfield inclusion is injective. The resulting sheaf
morphism is a monomorphism. Mathlib's finite-limit preservation for the constructed
point inverse image and scheme inverse image shows that their composite preserves
this monomorphism. Evaluation preserves monomorphisms, giving sectionwise injectivity.
(8) Use the already proved abelian coefficient colimit
`isColimitPadicAlgClRingObjCocone`. Its transition maps are injective since their
composites with the coefficient inclusions are injective. Apply the abelian comparison
above in its injective-transition case. Surjectivity of that comparison and stage
representatives for the section-group colimit give the union assertion.
(9) Induct on a finite set. The empty set uses the base field, and an insertion uses
a common upper bound of the field for the new element and the previous field.
Naturality of the coefficient inclusions transports both ranges into the common
field. For a finite family of finite matrices, apply this result to the range of
the function on the finite dependent sum of all entry positions. -/
theorem coefficient_finite_descent_sections (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (V : X.ProEt) [CompactSpace V.left] :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Function.Injective ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (Set.univ = ⋃ E : PadicAlgCl.FiniteIntermediateField l,
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (∀ S : Set ((padicAlgClRingObj X l).obj.obj (op V)), S.Finite →
      ∃ E : PadicAlgCl.FiniteIntermediateField l,
        S ⊆ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (∀ (K : Type v) [Finite K] (rows : K → Type w) (cols : K → Type z)
      [∀ k : K, Finite (rows k)] [∀ k : K, Finite (cols k)]
      (M : ∀ k : K, Matrix (rows k) (cols k)
        ((padicAlgClRingObj X l).obj.obj (op V))),
      ∃ E : PadicAlgCl.FiniteIntermediateField l,
        ∀ (k : K) (i : rows k) (j : cols k),
          M k i j ∈ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) := by
  classical
  let D := Profinite.padicSubfieldRingObjFunctor.{u} l ⋙ upperStarFromPoint X
  let c := padicAlgClRingObjCocone X l
  let ev := (sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V)
  have htrans : ∀ (i j : PadicAlgCl.FiniteIntermediateField l) (f : i ⟶ j)
      (U : X.ProEt), Function.Injective ((D.map f).hom.app (op U)) := by
    intro i j f U a b hab
    apply coefficient_section_injective X l i U
    have he := congrArg (fun g ↦ g.hom.app (op U))
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X l (leOfHom f))
    exact (ConcreteCategory.congr_hom he a).symm.trans
      ((congrArg ((padicSubfieldRingObjToPadicAlgCl X l j).hom.app (op U)) hab).trans
        (ConcreteCategory.congr_hom he b))
  have hbij := (abelian_sections_filtered_colimit X V
    (PadicAlgCl.FiniteIntermediateField l) D c (isColimitPadicAlgClRingObjCocone X l)).2
      (Or.inr htrans)
  have hrep (s : (padicAlgClRingObj X l).obj.obj (op V)) :
      ∃ E, s ∈ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) := by
    obtain ⟨t, ht⟩ := hbij.2 s
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨E, a, ha⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget AddCommGrpCat.{u + 1})
        (colimit.isColimit (D ⋙ ev))) t
    refine ⟨E, a, ?_⟩
    have he := ConcreteCategory.congr_hom (colimit.ι_desc (ev.mapCocone c) E) a
    exact he.symm.trans ((congrArg (colimit.desc (D ⋙ ev) (ev.mapCocone c)) ha).trans ht)
  have hmono {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) ⊆
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l F).hom.app (op V)) := by
    rintro s ⟨a, rfl⟩
    refine ⟨(padicSubfieldRingObjMap X l h).hom.app (op V) a, ?_⟩
    exact ConcreteCategory.congr_hom
      (congrArg (fun g ↦ g.hom.app (op V))
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X l h)) a
  have hfinite : ∀ S : Set ((padicAlgClRingObj X l).obj.obj (op V)), S.Finite →
      ∃ E, S ⊆ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V)) := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact ⟨Classical.arbitrary _, Set.empty_subset _⟩
    | @insert s S hs hS ih =>
      obtain ⟨E, hE⟩ := hrep s
      obtain ⟨F, hF⟩ := ih
      obtain ⟨G, hEG, hFG⟩ := exists_ge_ge E F
      exact ⟨G, Set.insert_subset ((hmono hEG) hE) (fun a ha ↦ hmono hFG (hF ha))⟩
  refine ⟨fun E ↦ coefficient_section_injective X l E V, ?_, hfinite, ?_⟩
  · symm
    apply Set.eq_univ_iff_forall.mpr
    intro s
    obtain ⟨E, hE⟩ := hrep s
    exact Set.mem_iUnion.mpr ⟨E, hE⟩
  · intro K _ rows cols _ _ M
    let entries : (Σ k : K, rows k × cols k) →
        (padicAlgClRingObj X l).obj.obj (op V) := fun p ↦ M p.1 p.2.1 p.2.2
    obtain ⟨E, hE⟩ := hfinite (Set.range entries) (Set.finite_range entries)
    exact ⟨E, fun k i j ↦ hE ⟨⟨k, i, j⟩, rfl⟩⟩


end AlgebraicGeometry.ProEtale
