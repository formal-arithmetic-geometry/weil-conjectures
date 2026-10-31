/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFpqcFiniteAffineTestCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.FpqcClosedImmersionDescent

/-!
# Fpqc descent of quasi-compactness and separatedness for algebraic spaces

Source: Stacks Project, `spaces-descent.tex`, Tags 041L and 0421, restricted to a scheme
base and scheme covering members (blueprint: lem-sfb-space-fpqc-qc-separated-descent).

The two implications are independent: separatedness is not a hypothesis of the first,
and quasi-compactness is not a hypothesis of the second. Schemes over `S` are objects
of `Over S`, and their functors of points are represented by `yoneda.obj`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

private theorem representableWith_comp_iso {S : Scheme.{u}}
    {G F H : (Over S)ᵒᵖ ⥤ Type u} (P : MorphismProperty (Over S))
    (a : G ⟶ F) (e : F ≅ H) (ha : IsRepresentableWith P a) :
    IsRepresentableWith P (a ≫ e.hom) := by
  intro T b
  obtain ⟨U, p, q, hq, hp⟩ := ha T (b ≫ e.inv)
  refine ⟨U, p, q, ?_, hp⟩
  exact hq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)

private theorem diagonal_representable {S : Scheme.{u}} (X : AlgebraicSpace S)
    {F : (Over S)ᵒᵖ ⥤ Type u} (f : X.obj.obj ⟶ F) :
    IsRepresentable (diagonalPresheafMap f) := by
  let k : Limits.pullback f f ⟶ X.obj.obj ⨯ X.obj.obj :=
    prod.lift (pullback.fst f f) (pullback.snd f f)
  have hd : IsPullback (𝟙 X.obj.obj) (diagonalPresheafMap f)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)) k := by
    apply IsPullback.mk' (by simp [diagonalPresheafMap, k])
    · intro W a b hab hba
      simpa using hab
    · intro W a b hab
      refine ⟨a, by simp, ?_⟩
      apply pullback.hom_ext
      · have := hab =≫ prod.fst
        simpa [k, diagonalPresheafMap] using this
      · have := hab =≫ prod.snd
        simpa [k, diagonalPresheafMap] using this
  intro T a
  obtain ⟨U, p, q, hq, hp⟩ := X.property.1 T (a ≫ k)
  let r := hd.lift q (yoneda.map p ≫ a) (by simpa using hq.w)
  exact ⟨U, p, r, IsPullback.of_right' hq hd, hp⟩

@[reassoc] private theorem diagonal_fst {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    diagonalPresheafMap f ≫ pullback.fst f f = 𝟙 G :=
  pullback.lift_fst _ _ _

@[reassoc] private theorem diagonal_snd {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    diagonalPresheafMap f ≫ pullback.snd f f = 𝟙 G :=
  pullback.lift_snd _ _ _

private theorem diagonal_baseChange {S : Scheme.{u}}
    {G F H : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) (g : H ⟶ F) :
    IsPullback (pullback.fst f g) (diagonalPresheafMap (pullback.snd f g))
      (diagonalPresheafMap f)
      (pullback.map _ _ _ _ (pullback.fst f g) (pullback.fst f g) g
        pullback.condition.symm pullback.condition.symm) := by
  let k := pullback.map (pullback.snd f g) (pullback.snd f g) f f
    (pullback.fst f g) (pullback.fst f g) g
    pullback.condition.symm pullback.condition.symm
  change IsPullback _ _ _ k
  apply IsPullback.mk' (by
    apply pullback.hom_ext <;>
      simp only [k, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        diagonal_fst, diagonal_snd, diagonal_fst_assoc, diagonal_snd_assoc,
        Category.comp_id])
  · intro W a b hab hba
    apply pullback.hom_ext
    · exact hab
    · have hab' : a = b := by
        simpa only [Category.assoc, diagonal_fst, Category.comp_id] using
          congrArg (fun t ↦ t ≫ pullback.fst _ _) hba
      exact congrArg (fun t ↦ t ≫ pullback.snd f g) hab'
  · intro W a b hab
    have hfst : a = b ≫ pullback.fst _ _ ≫ pullback.fst f g := by
      simpa only [k, pullback.map, Category.assoc, diagonal_fst, Category.comp_id,
        pullback.lift_fst] using congrArg (fun t ↦ t ≫ pullback.fst f f) hab
    have hsnd : a = b ≫ pullback.snd _ _ ≫ pullback.fst f g := by
      simpa only [k, pullback.map, Category.assoc, diagonal_snd, Category.comp_id,
        pullback.lift_snd] using congrArg (fun t ↦ t ≫ pullback.snd f f) hab
    let l : W ⟶ Limits.pullback f g := pullback.lift a
      (b ≫ pullback.fst _ _ ≫ pullback.snd f g) (by
        simpa only [Category.assoc, pullback.condition, pullback.condition_assoc] using
          congrArg (fun t ↦ t ≫ f) hfst)
    refine ⟨l, by simp [l], ?_⟩
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa only [l, Category.assoc, diagonal_fst_assoc, pullback.lift_fst] using hfst
      · simp only [l, Category.assoc, diagonal_fst_assoc, pullback.lift_snd]
    · apply pullback.hom_ext
      · simpa only [l, Category.assoc, diagonal_snd_assoc, pullback.lift_fst] using hsnd
      · simpa only [l, Category.assoc, diagonal_snd_assoc, pullback.lift_snd] using
          congrArg (fun t ↦ b ≫ t) (pullback.condition (f := pullback.snd f g)
            (g := pullback.snd f g))

private theorem separated_fpqc_descent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over S) (f : X.obj.obj ⟶ yoneda.obj T) {I : Type v}
    (Tᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hg : Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage T.left)
    (hsep : ∀ i, IsSeparatedPresheafMap (pullback.snd f (yoneda.map (g i)))) :
    IsSeparatedPresheafMap f := by
  intro R a
  obtain ⟨D, p, q, hD, _⟩ := diagonal_representable X f R a
  refine ⟨D, p, q, hD, ?_⟩
  let r : R ⟶ T := yoneda.preimage (a ≫ pullback.fst f f ≫ f)
  have hr : yoneda.map r = a ≫ pullback.fst f f ≫ f := yoneda.map_preimage _
  let Rᵢ (i : I) := Limits.pullback r (g i)
  let t (i : I) : Rᵢ i ⟶ R := pullback.fst r (g i)
  let s (i : I) : Rᵢ i ⟶ Tᵢ i := pullback.snd r (g i)
  have hR (i : I) : IsPullback (t i) (s i) r (g i) :=
    IsPullback.of_hasPullback _ _
  have hcov : Presieve.ofArrows (fun i ↦ (Rᵢ i).left) (fun i ↦ (t i).left) ∈
      Scheme.fpqcPrecoverage R.left :=
    Precoverage.mem_coverings_of_isPullback _ hg r.left
      (fun i ↦ (t i).left) (fun i ↦ (s i).left)
      (fun i ↦ (hR i).map (Over.forget S))
  have hlocal (i : I) : IsClosedImmersion (pullback.snd p.left (t i).left) := by
    let g' := yoneda.map (g i)
    have ht : yoneda.map (t i) ≫ a ≫ pullback.fst f f ≫ f =
        yoneda.map (s i) ≫ g' := by
      simpa only [Functor.map_comp, hr, Category.assoc] using
        congrArg (fun z ↦ yoneda.map z) (hR i).w
    have ht' : yoneda.map (t i) ≫ a ≫ pullback.snd f f ≫ f =
        yoneda.map (s i) ≫ g' := by
      rw [← pullback.condition]
      exact ht
    let b₁ := pullback.lift (yoneda.map (t i) ≫ a ≫ pullback.fst f f)
      (yoneda.map (s i)) (by simpa only [Category.assoc] using ht)
    let b₂ := pullback.lift (yoneda.map (t i) ≫ a ≫ pullback.snd f f)
      (yoneda.map (s i)) (by simpa only [Category.assoc] using ht')
    let b : yoneda.obj (Rᵢ i) ⟶
        Limits.pullback (pullback.snd f g') (pullback.snd f g') :=
      pullback.lift b₁ b₂ (by simp [b₁, b₂])
    obtain ⟨E, v, w, hE, hv⟩ := hsep i (Rᵢ i) b
    let k := pullback.map (pullback.snd f g') (pullback.snd f g') f f
      (pullback.fst f g') (pullback.fst f g') g'
      pullback.condition.symm pullback.condition.symm
    have hb : b ≫ k = yoneda.map (t i) ≫ a := by
      apply pullback.hom_ext <;> simp [b, b₁, b₂, k]
    have hglobal : IsPullback (w ≫ pullback.fst f g') (yoneda.map v)
        (diagonalPresheafMap f) (yoneda.map (t i) ≫ a) := by
      have hh := hE.paste_horiz (diagonal_baseChange f g')
      change IsPullback (w ≫ pullback.fst f g') (yoneda.map v)
        (diagonalPresheafMap f) (b ≫ k) at hh
      rwa [hb] at hh
    let z := hD.lift (w ≫ pullback.fst f g') (yoneda.map v ≫ yoneda.map (t i))
      (by simpa only [Category.assoc] using hglobal.w)
    let z' : E ⟶ D := yoneda.preimage z
    have hz : yoneda.map z' = z := yoneda.map_preimage _
    have hsq : IsPullback z' v p (t i) := by
      apply IsPullback.of_map_of_faithful yoneda
      rw [hz]
      exact IsPullback.of_right' hglobal hD
    have hv' : IsClosedImmersion v.left := hv
    have hsq' := hsq.map (Over.forget S)
    have he : IsIso hsq'.isoPullback.hom := inferInstance
    have hcomp : hsq'.isoPullback.hom ≫ pullback.snd p.left (t i).left = v.left :=
      hsq'.isoPullback_hom_snd
    rw [← hcomp] at hv'
    exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).mp hv'
  exact isClosedImmersion_of_fpqc_cover p.left (fun i ↦ (Rᵢ i).left)
    (fun i ↦ (t i).left) hcov hlocal

/-- Quasi-compactness and separatedness each descend along an fpqc family of schemes.
The predicates are the affine-scheme atlas test and closed-immersion diagonal test of
`lem-trf-space-qc-separated-etale-local`; no representability or finiteness of `f` is assumed.
Source: Stacks Project, `spaces-descent.tex`, Tags 041L and 0421
(blueprint: lem-sfb-space-fpqc-qc-separated-descent).

Proof, following the four steps of the node:
1. Assume all base changes are quasi-compact and fix an affine scheme test `Z → T`.
   The fibre products exist by `lem-trf-space-fibre-products-etale-covers`. Base change
   of the fpqc family is fpqc by `lem-weil-pbc-fpqc-covering-axioms`. The defining finite
   affine refinement in `def-weil-pbc-fpqc-covering` gives affine opens `W_j` in finitely
   many `Z ×_T T_i`, covering `Z`. The quasi-compactness hypothesis on each corresponding
   base change gives a quasi-compact scheme atlas of `X ×_T W_j`.
2. By `lem-a1-space-point-open-calculus`, the point maps of these finitely many spaces
   jointly cover `X ×_T Z` and are continuous. By `lem-a1-space-etale-open-image`, their
   point spaces are quasi-compact. Pull an arbitrary open cover back to each, choose
   finite subcovers, and take their finite union. Thus the point space of `X ×_T Z` is
   quasi-compact, so the same atlas criterion supplies a quasi-compact scheme atlas.
   An empty refinement forces `Z` and its pullback to be empty; use the empty atlas.
3. Independently assume all base changes are separated. Form `B = X ×_T X` by
   `lem-trf-space-fibre-products-etale-covers`. The relative diagonal is representable:
   on a scheme test `R → B`, the equality of the two maps `R → X` is represented by
   a scheme `D`, using the representable diagonal over `S` in `def-trf-algebraic-space`.
   The base change of `D → R` to `R ×_T T_i` is the corresponding scheme test of the
   diagonal of the base-changed morphism, hence is a closed immersion.
4. The schemes `R ×_T T_i` fpqc-cover `R` by `lem-weil-pbc-fpqc-covering-axioms`.
   Apply `lem-pc-fpqc-descend-closed-immersion` to `D → R`. It is a closed immersion
   for every scheme test `R`, which is precisely separatedness of `f`.
-/
theorem quasiCompact_separated_of_fpqc_scheme_cover
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) {I : Type v}
    (Tᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hg : Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage T.left) :
    ((∀ i, IsQuasiCompactPresheafMap (pullback.snd f (yoneda.map (g i)))) →
      IsQuasiCompactPresheafMap f) ∧
    ((∀ i, IsSeparatedPresheafMap (pullback.snd f (yoneda.map (g i)))) →
      IsSeparatedPresheafMap f) := by
  constructor
  · intro hqc Z hZ h
    obtain ⟨A, q, p, hA, n, i, W, w, B, b, c, r, hW, hsq, hcover⟩ :=
      fpqc_finite_affine_test_cover X T f Tᵢ g hg Z hZ h
    have hB (j : Fin n) : CompactSpace (Point (B j).obj.obj) := by
      obtain ⟨U, p', q', hp', hU, he, hs⟩ := hqc (i j) (W j) (hW j) (yoneda.map (w j))
      let a := pullback.lift q' (yoneda.map p') hp'
      let e := (hsq j).isoPullback
      exact (points_compactSpace_iff (B j)).mpr ⟨U, a ≫ e.inv, hU,
        representableWith_comp_iso _ a e.symm he,
        representableWith_comp_iso _ a e.symm hs⟩
    have hcompact : CompactSpace (Point A.obj.obj) := by
      have hc (j : Fin n) : IsCompact (Set.range (mapPoint (r j).hom.hom)) := by
        have := hB j
        exact isCompact_range (point_open_calculus.2.2.1 (B j) A (r j))
      have hu : (⋃ j, Set.range (mapPoint (r j).hom.hom)) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨j, y, hy⟩ := hcover x
        exact Set.mem_iUnion.mpr ⟨j, y, hy⟩
      exact isCompact_univ_iff.mp (hu ▸ isCompact_iUnion hc)
    obtain ⟨U, b, hU, hbE, hbS⟩ := (points_compactSpace_iff A).mp hcompact
    let v : U ⟶ Z := yoneda.preimage (b ≫ p)
    have hv : yoneda.map v = b ≫ p := yoneda.map_preimage _
    have hp : (b ≫ q) ≫ f = yoneda.map v ≫ h := by
      rw [hv, Category.assoc, hA.w, Category.assoc]
    have heq : pullback.lift (b ≫ q) (yoneda.map v) hp = b ≫ hA.isoPullback.hom := by
      apply pullback.hom_ext
      · simp
      · simp [hv]
    refine ⟨U, v, b ≫ q, hp, hU, ?_, ?_⟩
    · rw [heq]
      exact representableWith_comp_iso _ b hA.isoPullback hbE
    · rw [heq]
      exact representableWith_comp_iso _ b hA.isoPullback hbS
  · exact separated_fpqc_descent X T f Tᵢ g hg

end AlgebraicGeometry.AlgebraicSpace
