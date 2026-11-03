/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Finite descent of coefficient sections

Source: Stacks Project, Tag 0738, and the current blueprint, sec-six-functors-basics,
sk-lem-lisse-finite-descent/sk-lem-coefficient-finite-descent-sections
(blueprint: det-lem-coefficient-finite-descent-sections).

The general comparison is injective on quasi-compact objects and bijective if the object
is quasi-separated or the transitions are sectionwise injective. The coefficient conclusion
uses only quasi-compactness. Its maps are the legs of the specified coefficient cocone.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem affine_refinement (X : Scheme.{u}) (W : X.ProEt)
    [IsAffine W.left] (S : Sieve W) (hS : S ∈ Scheme.ProEt.topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W ∧ (∀ i, S (f i)) ∧
        ∀ i, IsAffine (V i).left := by
  classical
  have : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [Scheme.ProEt.precoverage]
    infer_instance
  have : (Scheme.ProEt.precoverage X).HasIsos := by dsimp [Scheme.ProEt.precoverage]; infer_instance
  have : (Scheme.ProEt.precoverage X).IsStableUnderBaseChange := by
    dsimp [Scheme.ProEt.precoverage]
    infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (Scheme.ProEt.precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let E := T.preZeroHypercover
  let F := Scheme.ProEt.forget X ⋙ Over.forget X
  let E' := E.map F
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage W.left := by
    have he : E'.presieve₀ = Presieve.map F T := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map F) T.presieve₀_preZeroHypercover
    rw [he]
    exact hT
  let U : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover U.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨A, r, hfin, _⟩ := QuasiCompactCover.exists_hom U
  let := hfin
  have (i : A.I₀) : WeaklyEtale (A.f i) := A.cover.map_prop i
  let V : A.I₀ → X.ProEt := fun i ↦ Scheme.ProEt.mk (A.f i ≫ W.hom)
  let f : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (A.f i) (by rfl)
  refine ⟨A.I₀, hfin, V, f, ?_, ?_, fun i ↦ ?_⟩
  rotate_left 2
  · change IsAffine (Spec (A.X i))
    infer_instance
  · apply Precoverage.generate_mem_toGrothendieck
    change Presieve.map F (Presieve.ofArrows V f) ∈ Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    change A.cover.presieve₀ ∈ Scheme.proetalePrecoverage W.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, A.cover.mem₀⟩
  · intro i
    let e := r.s₀ i
    let g : V i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = A.f i ≫ W.hom
      have he : r.h₀ i ≫ (E.f e).left = A.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (Scheme.ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hTS _ _ e.2) g

private theorem finite_affine_refinement
    (X : Scheme.{u}) (W : X.ProEt) [CompactSpace W.left]
    (S : Sieve W) (hS : S ∈ Scheme.ProEt.topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W ∧ (∀ i, S (f i)) ∧
        ∀ i, IsAffine (V i).left := by
  classical
  let A := W.left.affineCover.finiteSubcover
  let V (i : A.I₀) := Scheme.ProEt.ofOpenImmersion W (A.f i)
  let f (i : A.I₀) : V i ⟶ W := Scheme.ProEt.ofOpenImmersionHom W (A.f i)
  have (i : A.I₀) : IsAffine (V i).left := by
    change IsAffine (A.X i)
    dsimp [A]
    infer_instance
  have hV : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W := by
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (A.f ·)
    · intro x
      exact ⟨A.idx x, A.covers x⟩
    · intro i
      exact Sieve.ofArrows_mk V f i
  choose K hK U g hg hSg hUa using fun i ↦
    affine_refinement X (V i) (S.pullback (f i))
      ((Scheme.ProEt.topology X).pullback_stable (f i) hS)
  have (i : A.I₀) : Finite (K i) := hK i
  refine ⟨Σ i, K i, inferInstance, (fun p ↦ U p.1 p.2),
    (fun p ↦ g p.1 p.2 ≫ f p.1), ?_, (fun p ↦ hSg p.1 p.2),
    (fun p ↦ hUa p.1 p.2)⟩
  have h := (Scheme.ProEt.topology X).bindOfArrows hV hg
  rwa [Presieve.bindOfArrows_ofArrows] at h

section SetComparison

variable {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
  (F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))

private noncomputable abbrev sectionPresheaf :=
  colimit (F ⋙ sheafToPresheaf (Scheme.ProEt.topology X) (Type (u + 1)))

private noncomputable abbrev sectionComparison :
    sectionPresheaf F ⟶ (colimit F).obj :=
  colimit.desc _ ((sheafToPresheaf _ _).mapCocone (colimit.cocone F))

private theorem sectionComparison_fac (i : I) :
    colimit.ι (F ⋙ sheafToPresheaf _ _) i ≫ sectionComparison F =
      (colimit.ι F i).hom := colimit.ι_desc _ i

private theorem sectionComparison_fac_apply (i : I) (W : X.ProEt)
    (x : (F.obj i).obj.obj (op W)) :
    (sectionComparison F).app (op W)
      ((colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op W) x) =
        (colimit.ι F i).hom.app (op W) x := by
  exact congrArg (fun η : (F.obj i).obj ⟶ (colimit F).obj ↦ η.app (op W) x)
    (sectionComparison_fac F i)

private theorem sectionComparison_local :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (sectionComparison F) ∧
      Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (sectionComparison F) := by
  let J := Scheme.ProEt.topology X
  let U := sheafToPresheaf J (Type (u + 1))
  let L := presheafToSheaf J (Type (u + 1))
  let adj := sheafificationAdjunction J (Type (u + 1))
  let P := colimit.cocone (F ⋙ U)
  let hP := colimit.isColimit (F ⋙ U)
  let hQ := isColimitOfPreserves L hP
  let e : (F ⋙ U) ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit)
  let hc := (IsColimit.precomposeHomEquiv e (colimit.cocone F)).symm
    (colimit.isColimit F)
  let θ := hQ.coconePointUniqueUpToIso hc
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : I) : P.ι.app i ≫ k = U.map (colimit.ι F i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (F.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hc i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (F.obj i) ≫ colimit.ι F i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : sectionComparison F = k := by
    apply hP.hom_ext
    intro i
    exact (sectionComparison_fac F i).trans (hk i).symm
  rw [heq]
  have : J.WEqualsLocallyBijective (Type (u + 1)) :=
    by infer_instance
  change Presheaf.IsLocallyInjective J
    (toSheafify J P.pt ≫ U.map θ.hom) ∧
      Presheaf.IsLocallySurjective J (toSheafify J P.pt ≫ U.map θ.hom)
  constructor <;> infer_instance

variable [IsFiltered I]

private theorem finite_common_stage {K : Type*} [Finite K] (i : K → I) :
    ∃ j, Nonempty (∀ k, i k ⟶ j) := by
  classical
  let := Fintype.ofFinite K
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  exact ⟨j, ⟨fun k ↦ (hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)).some⟩⟩

private theorem eventual_equality (W : X.ProEt) [CompactSpace W.left]
    (i : I) (x y : (F.obj i).obj.obj (op W))
    (h : (colimit.ι F i).hom.app (op W) x = (colimit.ι F i).hom.app (op W) y) :
    ∃ (j : I) (f : i ⟶ j), (F.map f).hom.app (op W) x =
      (F.map f).hom.app (op W) y := by
  classical
  let P := sectionPresheaf F
  let q := sectionComparison F
  let η := colimit.ι (F ⋙ sheafToPresheaf _ _) i
  have : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) q :=
    (sectionComparison_local F).1
  have heq : q.app (op W) (η.app (op W) x) = q.app (op W) (η.app (op W) y) := by
    exact (sectionComparison_fac_apply F i W x).trans
      (h.trans (sectionComparison_fac_apply F i W y).symm)
  obtain ⟨K, hK, V, f, hcover, hf, _⟩ := finite_affine_refinement X W
    (Presheaf.equalizerSieve (η.app (op W) x) (η.app (op W) y))
    (Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X) q _ _ heq)
  let := hK
  have hevent (k : K) : ∃ (j : I) (g : i ⟶ j),
      (F.map g).hom.app (op (V k)) ((F.obj i).obj.map (f k).op x) =
        (F.map g).hom.app (op (V k)) ((F.obj i).obj.map (f k).op y) := by
    let ev := (evaluation X.ProEtᵒᵖ (Type (u + 1))).obj (op (V k))
    have hh := hf k
    change P.map (f k).op (η.app (op W) x) =
      P.map (f k).op (η.app (op W) y) at hh
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at hh
    exact (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves ev (colimit.isColimit (F ⋙ sheafToPresheaf _ _))) _ _).mp hh
  choose j g hg using hevent
  obtain ⟨j', g', k, hk⟩ := IsFiltered.wideSpan g
  refine ⟨j', g', ?_⟩
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (F.obj j').property).isSheafFor
    (Presieve.ofArrows V f) hcover).isSeparatedFor.ext
  rintro Z a ⟨l⟩
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  have hh := congrArg ((F.map (k l)).hom.app (op (V l))) (hg l)
  change ((F.map (g l) ≫ F.map (k l)).hom.app (op (V l)))
      ((F.obj i).obj.map (f l).op x) =
    ((F.map (g l) ≫ F.map (k l)).hom.app (op (V l)))
      ((F.obj i).obj.map (f l).op y) at hh
  rw [← F.map_comp, hk] at hh
  exact hh

end SetComparison

section SetGluing

variable {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  (F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))

private theorem local_sections (W : X.ProEt) [CompactSpace W.left]
    (s : (colimit F).obj.obj (op W)) :
    ∃ (K : Type (u + 1)) (_ : Finite K) (V : K → X.ProEt) (f : ∀ k, V k ⟶ W),
      Sieve.ofArrows V f ∈ Scheme.ProEt.topology X W ∧ (∀ k, IsAffine (V k).left) ∧
      ∃ (i : I) (t : ∀ k, (F.obj i).obj.obj (op (V k))),
        ∀ k, (colimit.ι F i).hom.app (op (V k)) (t k) = (colimit F).obj.map (f k).op s := by
  classical
  let P := sectionPresheaf F
  let q := sectionComparison F
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) q :=
    (sectionComparison_local F).2
  obtain ⟨K, hK, V, f, hcover, hf, hVa⟩ := finite_affine_refinement X W
    (Presheaf.imageSieve q s) (Presheaf.imageSieve_mem _ q s)
  let := hK
  have hrep (k : K) : ∃ (i : I) (t : (F.obj i).obj.obj (op (V k))),
      (colimit.ι F i).hom.app (op (V k)) t = (colimit F).obj.map (f k).op s := by
    obtain ⟨a, ha⟩ := hf k
    let ev := (evaluation X.ProEtᵒᵖ (Type (u + 1))).obj (op (V k))
    obtain ⟨i, t, ht⟩ := Types.jointly_surjective _
      (isColimitOfPreserves ev (colimit.isColimit (F ⋙ sheafToPresheaf _ _))) a
    change (colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op (V k)) t = a at ht
    refine ⟨i, t, ?_⟩
    have hh := sectionComparison_fac_apply F i (V k) t
    change q.app (op (V k))
      ((colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op (V k)) t) = _ at hh
    rw [ht] at hh
    exact hh.symm.trans ha
  choose i t ht using hrep
  obtain ⟨j, ⟨g⟩⟩ := finite_common_stage i
  refine ⟨K, hK, V, f, hcover, hVa, j,
    (fun k ↦ (F.map (g k)).hom.app (op (V k)) (t k)), fun k ↦ ?_⟩
  have hh := congrArg (fun h ↦ h.hom.app (op (V k))) (colimit.w F (g k))
  exact (ConcreteCategory.congr_hom hh (t k)).trans (ht k)

private theorem stage_injective
    (ht : ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
      Function.Injective ((F.map f).hom.app (op U)))
    (W : X.ProEt) (i : I) : Function.Injective ((colimit.ι F i).hom.app (op W)) := by
  intro x y h
  let P := sectionPresheaf F
  let q := sectionComparison F
  let η := colimit.ι (F ⋙ sheafToPresheaf _ _) i
  have : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) q :=
    (sectionComparison_local F).1
  have heq : q.app (op W) (η.app (op W) x) = q.app (op W) (η.app (op W) y) := by
    exact (sectionComparison_fac_apply F i W x).trans
      (h.trans (sectionComparison_fac_apply F i W y).symm)
  let S : Sieve W := Presheaf.equalizerSieve (F := P)
    (η.app (op W) x) (η.app (op W) y)
  have hS : S ∈ Scheme.ProEt.topology X W :=
    Presheaf.equalizerSieve_mem _ q _ _ heq
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (F.obj i).property) S hS).isSeparatedFor.ext
  intro Z f hf
  have hh := hf
  change P.map f.op (η.app (op W) x) = P.map f.op (η.app (op W) y) at hh
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at hh
  let ev := (evaluation X.ProEtᵒᵖ (Type (u + 1))).obj (op Z)
  obtain ⟨j, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ev (colimit.isColimit (F ⋙ sheafToPresheaf _ _))) _ _).mp hh
  exact ht i j g Z hg

private theorem section_representative (W : X.ProEt) [CompactSpace W.left]
    (h : QuasiSeparatedSpace W.left ∨
      (∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
        Function.Injective ((F.map f).hom.app (op U))))
    (s : (colimit F).obj.obj (op W)) :
    ∃ (i : I) (t : (F.obj i).obj.obj (op W)), (colimit.ι F i).hom.app (op W) t = s := by
  classical
  obtain ⟨K, hK, V, f, hcover, hVa, i, t, ht⟩ := local_sections F W s
  let := hK
  have (k : K) : IsAffine (V k).left := hVa k
  have himage (k l : K) (Z : X.ProEt) (a : Z ⟶ V k) (b : Z ⟶ V l)
      (hab : a ≫ f k = b ≫ f l) :
      (colimit.ι F i).hom.app (op Z) ((F.obj i).obj.map a.op (t k)) =
        (colimit.ι F i).hom.app (op Z) ((F.obj i).obj.map b.op (t l)) := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht, ht]
    simp only [← types_comp_apply, ← Functor.map_comp, ← op_comp, hab]
  have hmatching : ∃ (j : I) (g : i ⟶ j),
      Presieve.Arrows.Compatible (F.obj j).obj f
        (fun k ↦ (F.map g).hom.app (op (V k)) (t k)) := by
    rcases h with hqs | hmono
    · let := hqs
      have hcompact (k l : K) : CompactSpace (pullback (f k) (f l)).left := by
        have hp := (IsPullback.of_hasPullback (f k) (f l)).map
          (Scheme.ProEt.forget X ⋙ Over.forget X)
        have hqc : QuasiCompact ((Scheme.ProEt.forget X ⋙ Over.forget X).map (f k)) := by
          change QuasiCompact (f k).left
          infer_instance
        have hqc' : QuasiCompact ((Scheme.ProEt.forget X ⋙ Over.forget X).map
            (pullback.snd (f k) (f l))) := MorphismProperty.of_isPullback hp hqc
        have : QuasiCompact (pullback.snd (f k) (f l)).left := hqc'
        exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd (f k) (f l)).left
      have hev (p : K × K) : ∃ (j : I) (g : i ⟶ j),
          (F.map g).hom.app (op (pullback (f p.1) (f p.2)))
            ((F.obj i).obj.map (pullback.fst (f p.1) (f p.2)).op (t p.1)) =
          (F.map g).hom.app (op (pullback (f p.1) (f p.2)))
            ((F.obj i).obj.map (pullback.snd (f p.1) (f p.2)).op (t p.2)) := by
        let := hcompact p.1 p.2
        exact eventual_equality F _ i _ _ (himage _ _ _ _ _ pullback.condition)
      choose j g hg using hev
      obtain ⟨j', g', k, hk⟩ := IsFiltered.wideSpan g
      refine ⟨j', g', (Presieve.Arrows.pullbackCompatible_iff _ _ _).mpr ?_⟩
      intro a b
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      have hh := congrArg ((F.map (k (a, b))).hom.app (op (pullback (f a) (f b))))
        (hg (a, b))
      change ((F.map (g (a, b)) ≫ F.map (k (a, b))).hom.app
          (op (pullback (f a) (f b))))
            ((F.obj i).obj.map (pullback.fst (f a) (f b)).op (t a)) =
        ((F.map (g (a, b)) ≫ F.map (k (a, b))).hom.app
          (op (pullback (f a) (f b))))
            ((F.obj i).obj.map (pullback.snd (f a) (f b)).op (t b)) at hh
      rw [← F.map_comp, hk] at hh
      exact hh
    · refine ⟨i, 𝟙 i, ?_⟩
      simp only [F.map_id]
      change Presieve.Arrows.Compatible (F.obj i).obj f t
      intro k l Z a b hab
      exact stage_injective F hmono Z i (himage k l Z a b hab)
  obtain ⟨j, g, hmatch⟩ := hmatching
  obtain ⟨t', ht', _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
    (((isSheaf_iff_isSheaf_of_type _ _).mp (F.obj j).property).isSheafFor
      (Presieve.ofArrows V f) hcover) _ hmatch
  refine ⟨j, t', ?_⟩
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (colimit F).property).isSheafFor
    (Presieve.ofArrows V f) hcover).isSeparatedFor.ext
  rintro Z a ⟨k⟩
  rw [← NatTrans.naturality_apply, ht']
  have hh := congrArg (fun h ↦ h.hom.app (op (V k))) (colimit.w F g)
  exact (ConcreteCategory.congr_hom hh (t k)).trans (ht k)

end SetGluing

/-- Source: Stacks Project, Tag 0738 (2)--(4), specialized to the small pro-etale site
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: form the sectionwise presheaf colimit and identify its sheafification with the sheaf
colimit, using lem-weil-pbc-presheaf-colimits-sectionwise and
lem-weil-pbc-site-sheafification-sections-local. Equality in the sheafification is local.
Refine this equality cover to a finite affine cover using quasi-compactness, the affine-open
basis, and the fpqc condition of sk-def-pe-site. Filteredness moves all the finitely many
witnesses to one stage and equalizes their parallel arrows. Separatedness at that stage
proves injectivity. For surjectivity on a qcqs object, lift a section locally, take a finite
affine refinement, and put its lifts at one stage. The overlaps are quasi-compact: maps from
affine schemes to a quasi-separated scheme
are quasi-compact, and quasi-compactness is preserved by pullback. Injectivity there lets
filteredness make
the matching equations hold at one later stage. The sheaf axiom then glues the lifts.
If transitions are injective on every object, every stage maps injectively to sheafification
on every object: local equality after transition implies local equality before transition,
and separatedness gives equality. The finite-stage local lifts therefore agree on all
overlaps without any quasi-separatedness assumption, and glue. -/
theorem filteredColimit_sections_sets
    (X : Scheme.{u}) (V : X.ProEt) [CompactSpace V.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
    Function.Injective
      (colimit.post F ((sheafSections (Scheme.ProEt.topology X) (Type (u + 1))).obj (op V))) ∧
    ((QuasiSeparatedSpace V.left ∨
      (∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
        Function.Injective ((F.map f).hom.app (op U)))) →
      Function.Bijective
        (colimit.post F ((sheafSections (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (op V)))) := by
  let A := (sheafSections (Scheme.ProEt.topology X) (Type (u + 1))).obj (op V)
  have hfac (i : I) (t : (F.obj i).obj.obj (op V)) :
      (colimit.post F A) ((colimit.ι (F ⋙ A) i) t) =
        (colimit.ι F i).hom.app (op V) t :=
    ConcreteCategory.congr_hom (colimit.ι_post F A i) t
  have hinj : Function.Injective (colimit.post F A) := by
    intro x y h
    obtain ⟨i, a, b, rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit (F ⋙ A)) x y
    have he : (colimit.ι F i).hom.app (op V) a =
        (colimit.ι F i).hom.app (op V) b := by
      exact (hfac i a).symm.trans (h.trans (hfac i b))
    obtain ⟨j, f, hf⟩ := eventual_equality F V i a b he
    exact (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (F ⋙ A)) a b).mpr
      ⟨j, f, hf⟩
  refine ⟨hinj, fun h ↦ ⟨hinj, fun s ↦ ?_⟩⟩
  obtain ⟨i, t, ht⟩ := section_representative F V h s
  refine ⟨(colimit.ι (F ⋙ A) i) t, ?_⟩
  exact (hfac i t).trans ht


/-- Source: Stacks Project, Tags 0738, 00YR and 03CO; the abelian version of the comparison
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: forgetting abelian groups to sets preserves filtered colimits. The natural
isomorphism sheafComposeNatIso expresses its compatibility with sheafification. The fully
faithful sheafification adjunction then transfers filtered-colimit preservation to the
functor forgetting abelian sheaves to set sheaves. Compare the canonical maps by the two
factorizations of colimit.post for the composite of forgetting and evaluation. The
forgetful comparison and the evaluation of the sheaf-forgetful comparison are bijections.
Cancel them to transfer the injectivity and the conditional bijectivity from
filteredColimit_sections_sets to the additive comparison. -/
theorem filteredColimit_sections_abelian
    (X : Scheme.{u}) (V : X.ProEt) [CompactSpace V.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    Function.Injective
      (colimit.post F ((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (op V))) ∧
    ((QuasiSeparatedSpace V.left ∨
      (∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
        Function.Injective ((F.map f).hom.app (op U)))) →
      Function.Bijective
        (colimit.post F ((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (op V)))) := by
  let J := Scheme.ProEt.topology X
  let U := CategoryTheory.forget AddCommGrpCat.{u + 1}
  let T := sheafCompose J U
  have : PreservesColimitsOfShape I U := by infer_instance
  have : PreservesColimitsOfShape I T := by
    apply (sheafificationAdjunction J AddCommGrpCat.{u + 1}).preservesColimitsOfShape_iff T I |>.mpr
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J U (sheafificationAdjunction J AddCommGrpCat.{u + 1})
        (sheafificationAdjunction J (Type (u + 1))))
  let A := (sheafSections J AddCommGrpCat.{u + 1}).obj (op V)
  let B := (sheafSections J (Type (u + 1))).obj (op V)
  let a := colimit.post (F ⋙ T) B
  let b := B.map (colimit.post F T)
  let c := colimit.post (F ⋙ A) U
  let d := U.map (colimit.post F A)
  have hb : Function.Bijective b := (isIso_iff_bijective b).mp (by
    dsimp [b]; infer_instance)
  have hc : Function.Bijective c := (isIso_iff_bijective c).mp (by
    dsimp [c]; infer_instance)
  have heq : a ≫ b = c ≫ d := by
    dsimp [a, b, c, d]
    rw [colimit.post_post, colimit.post_post]
    rfl
  obtain ⟨hinj, hbij⟩ := filteredColimit_sections_sets X V I (F ⋙ T)
  have hinj' : Function.Injective d := by
    intro x y h
    obtain ⟨x', rfl⟩ := hc.2 x
    obtain ⟨y', rfl⟩ := hc.2 y
    apply congrArg c
    apply hinj
    apply hb.1
    exact (ConcreteCategory.congr_hom heq x').trans
      (h.trans (ConcreteCategory.congr_hom heq y').symm)
  refine ⟨hinj', fun h ↦ ⟨hinj', ?_⟩⟩
  have ha : Function.Bijective a := hbij h
  intro z
  obtain ⟨x, hx⟩ := ha.2 ((inv (B.map (colimit.post F T))) z)
  refine ⟨c x, ?_⟩
  have hh := ConcreteCategory.congr_hom heq x
  change b (a x) = d (c x) at hh
  change d (c x) = z
  rw [← hh, hx]
  exact IsIso.inv_hom_id_apply (B.map (colimit.post F T)) z


end AlgebraicGeometry.ProEtale
