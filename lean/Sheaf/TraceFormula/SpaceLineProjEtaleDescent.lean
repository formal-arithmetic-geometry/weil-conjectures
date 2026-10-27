/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.TraceFormula.SpaceLineModuleProjMap
import Sheaf.TraceFormula.SpaceLineTestBaseChange
import Sheaf.TraceFormula.SpaceMapOpenProjBaseChange
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Descending everywhere-defined canonical Proj maps

Source: Stacks Project, Tags 0D3C, 0D2Z and 01O9
(blueprint: lem-trf-space-line-proj-etale-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

private theorem subsheaf_eq_top_of_scheme_cover
    (X : AlgebraicSpace S) (U : Subfunctor X.obj.obj)
    (hU : Presheaf.IsSheaf (Scheme.fppfTopology.over S) U.toFunctor)
    (T : Over S) (f : X.obj.obj ⟶ yoneda.obj T)
    (I : Type v) (Tᵢ Xᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hcover : ∀ (V : Over S) (x : V ⟶ T),
      ∃ R : Sieve V.left, R ∈ Scheme.fppfTopology V.left ∧
        ∀ (W : Over S) (a : W ⟶ V), R a.left →
          ∃ (i : I) (b : W ⟶ Tᵢ i), b ≫ g i = a ≫ x)
    (k : ∀ i, yoneda.obj (Xᵢ i) ⟶ X.obj.obj) (fᵢ : ∀ i, Xᵢ i ⟶ Tᵢ i)
    (hcart : ∀ i, IsPullback (k i) (yoneda.map (fᵢ i)) f (yoneda.map (g i)))
    (hlocal : ∀ i, U.preimage (k i) = ⊤) : U = ⊤ := by
  apply top_unique
  intro V s _
  apply (U.isSheaf_iff ((isSheaf_iff_isSheaf_of_type _ _).1 X.obj.property)).1
    ((isSheaf_iff_isSheaf_of_type _ _).1 hU)
  obtain ⟨R, hR, hlift⟩ := hcover V.unop (f.app V s)
  apply (Scheme.fppfTopology.over S).superset_covering (S := (Sieve.overEquiv V.unop).symm R)
  · intro W a ha
    obtain ⟨i, b, hb⟩ := hlift W a ha
    let t := X.obj.obj.map a.op s
    have hw : yonedaEquiv.symm t ≫ f = yoneda.map b ≫ yoneda.map (g i) := by
      rw [yonedaEquiv_symm_naturality_right, ← Functor.map_comp]
      have hn := f.naturality_apply a.op s
      change f.app (op W) t = a ≫ f.app V s at hn
      rw [hn, ← hb]
      exact (yonedaEquiv.symm_apply_apply (yoneda.map (b ≫ g i)))
    let l := (hcart i).lift (yonedaEquiv.symm t) (yoneda.map b) hw
    let c : W ⟶ Xᵢ i := yoneda.preimage l
    have hc : (k i).app (op W) c = t := by
      have he : yoneda.map c ≫ k i = yonedaEquiv.symm t := by
        rw [Functor.map_preimage]
        exact (hcart i).lift_fst _ _ _
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map,
        Equiv.apply_symm_apply] using congrArg yonedaEquiv he
    change t ∈ U.obj (op W)
    rw [← hc]
    change c ∈ (U.preimage (k i)).obj (op W)
    rw [hlocal i]
    trivial
  · exact Scheme.fppfTopology.overEquiv_symm_mem_over V.unop R hR

private theorem canonical_test_of_map
    {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} {f : F ⟶ yoneda.obj T}
    {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (U : Subfunctor F)
    (r : U.toFunctor ⟶ yoneda.obj (projOver T A)) (hr : ψ.IsCanonicalMap U r)
    (W : Over S) (a : U.toFunctor.obj (op W)) :
    ψ.IsCanonicalTestMap (CostructuredArrow.mk (yonedaEquiv.symm a.val))
      (r.app (op W) a) := by
  constructor
  · exact hr.1 W a
  · intro Z j C h e α hα hi
    let b : U.toFunctor.obj (op Z.left) := U.toFunctor.map j.left.op a
    have hb : yonedaEquiv.symm b.val = Z.hom := by
      change yonedaEquiv.symm (F.map j.left.op a.val) = Z.hom
      rw [← yonedaEquiv_symm_naturality_left]
      exact CostructuredArrow.w j
    have hv := hr.2 Z.left b C
    have hn := r.naturality_apply j.left.op a
    change r.app (op Z.left) b = j.left ≫ r.app (op W) a at hn
    rw [hn, hb] at hv
    exact hv h e α hα hi

/-- Canonical maps of an arbitrary graded line map descend from an etale covering.
This assertion uses no section algebra or quasi-compactness assumption.

Source: Stacks, Descent on Spaces, Tag 0D3C, from U(psi)=X to the global open immersion;
Divisors on Spaces, Tag 0D2Z(3)
(blueprint: lem-trf-space-line-proj-etale-descent).

Proof: apply space_line_module_proj_map to obtain the open subspace U and its unique
canonical map. On each Cartesian scheme chart its base-change clause identifies the
inverse image of U with the local generation locus, which is top by hypothesis. Any
scheme test of X lifts fppf locally to one of these charts: use hcover on its composite
with f, then the universal property hcart. Membership in U is local, since U and X are
sheaves and U is a subfunctor. Thus U is top, including when the cover is empty. Transport
the canonical map across this equality. Uniqueness in the scheme-chart clause identifies
the local canonical maps with the supplied r_i, giving the displayed section equation.
PullbackData.isPullback identifies the local Proj with the fibre product of the global
Proj and T_i. Pasting this square with hcart and using the structural equation of the
canonical map identifies the inverse image of the local Proj with X_i. The local Proj
maps form an etale cover of the global Proj: etaleness is stable under base change and
hcover supplies the local lifts. If the given family has a larger index universe, refine
it by a small family of affine etale charts of the target; the target and its affine
basis are small. Apply isOpenImmersion_of_etale_cover to this cover, using hopen on
each pullback. This proves representability with open-immersion scheme tests. -/
theorem space_line_proj_etale_descent
    (S : Scheme.{u}) (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T) (A : T.left.GradedAlgebraData)
    (L : X.Modules) (hL : X.IsLineModule L)
    (ψ : GradedLineMap f A (lineTestFamily X L hL))
    (I : Type v) (Tᵢ Xᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hget : ∀ i, Etale (g i).left)
    (hcover : ∀ (V : Over S) (x : V ⟶ T),
      ∃ R : Sieve V.left, R ∈ Scheme.fppfTopology V.left ∧
        ∀ (W : Over S) (a : W ⟶ V), R a.left →
          ∃ (i : I) (b : W ⟶ Tᵢ i), b ≫ g i = a ≫ x)
    (k : ∀ i, yoneda.obj (Xᵢ i) ⟶ X.obj.obj) (fᵢ : ∀ i, Xᵢ i ⟶ Tᵢ i)
    (hcart : ∀ i, IsPullback (k i) (yoneda.map (fᵢ i)) f (yoneda.map (g i)))
    (Aᵢ : ∀ i, (Tᵢ i).left.GradedAlgebraData)
    (D : ∀ i, Scheme.GradedAlgebraData.PullbackData (g i).left A (Aᵢ i))
    (ψᵢ : ∀ i, GradedLineMap (yoneda.map (fᵢ i)) (Aᵢ i)
      ((lineTestFamily X L hL).pullback (k i)))
    (hbase : ∀ i, ψ.IsBaseChange (k i) (g i) (D i) (ψᵢ i))
    (rᵢ : ∀ i, Xᵢ i ⟶ projOver (Tᵢ i) (Aᵢ i))
    (hgen : ∀ i, (ψᵢ i).IsGenerationOpen ⊤)
    (hcanonical : ∀ i, (ψᵢ i).IsCanonicalMap ⊤
      ((⊤ : Subfunctor (yoneda.obj (Xᵢ i))).ι ≫ yoneda.map (rᵢ i)))
    (hopen : ∀ i, IsOpenImmersion (rᵢ i).left) :
    ψ.IsGenerationOpen ⊤ ∧
      ∃ r : X.obj.obj ⟶ yoneda.obj (projOver T A),
        ψ.IsCanonicalMap ⊤ ((⊤ : Subfunctor X.obj.obj).ι ≫ r) ∧
        IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) r ∧
        ∀ (i : I) (W : Over S) (a : W ⟶ Xᵢ i),
          (a ≫ rᵢ i).left ≫ (D i).relProjComparison =
            (r.app (op W) ((k i).app (op W) a)).left := by
  classical
  obtain ⟨U, hU, _, _, hgenU, rU, ⟨hrU, hbc⟩, _⟩ :=
    space_line_module_proj_map S T X f A L hL ψ
  have hlocal (i : I) : U.preimage (k i) = ⊤ := by
    obtain ⟨hu, _⟩ := hbc (Xᵢ i) (Tᵢ i) (g i) (fᵢ i) (k i) (hcart i).w
      (Aᵢ i) (D i) (ψᵢ i) (hbase i)
    apply top_unique
    intro W a _
    exact (hu W.unop a).2 ((hgen i W.unop a).1 trivial)
  have htop : U = ⊤ := subsheaf_eq_top_of_scheme_cover X U hU T f
    I Tᵢ Xᵢ g hcover k fᵢ hcart hlocal
  subst U
  let r : X.obj.obj ⟶ yoneda.obj (projOver T A) := inv (⊤ : Subfunctor X.obj.obj).ι ≫ rU
  have hcomp : (⊤ : Subfunctor X.obj.obj).ι ≫ r = rU := by simp [r]
  have hr : ψ.IsCanonicalMap ⊤ ((⊤ : Subfunctor X.obj.obj).ι ≫ r) := hcomp.symm ▸ hrU
  have hmap (i : I) (W : Over S) (a : W ⟶ Xᵢ i) :
      (a ≫ rᵢ i).left ≫ (D i).relProjComparison =
        (r.app (op W) ((k i).app (op W) a)).left := by
    have hcoh : (lineTestFamily X L hL).IsCoherent := by
      change (linePresentation X L hL).toTestLineFamily.IsCoherent
      exact (linePresentation X L hL).coherent
    obtain ⟨_, hm⟩ := space_line_test_base_change hcoh ψ
      (k i) (g i) (hcart i).w (D i) (ψᵢ i) (hbase i)
    let test : SchemeTests (yoneda.obj (Xᵢ i)) := CostructuredArrow.mk (yoneda.map a)
    have ha : yonedaEquiv.symm a = yoneda.map a := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    have hk : yonedaEquiv.symm ((k i).app (op W) a) = yoneda.map a ≫ k i := by
      rw [← yonedaEquiv_symm_naturality_right, ha]
    apply hm test
    · have ht := (hgen i W a).1 trivial
      change (ψᵢ i).generationSet (CostructuredArrow.mk (yonedaEquiv.symm a)) = Set.univ at ht
      rw [ha] at ht
      exact ht
    · have ht := canonical_test_of_map ψ ⊤
        ((⊤ : Subfunctor X.obj.obj).ι ≫ r) hr W
        ⟨(k i).app (op W) a, trivial⟩
      change ψ.IsCanonicalTestMap
        (CostructuredArrow.mk (yonedaEquiv.symm ((k i).app (op W) a)))
        (r.app (op W) ((k i).app (op W) a)) at ht
      rw [hk] at ht
      exact ht
    · have ht := canonical_test_of_map (ψᵢ i) ⊤
        ((⊤ : Subfunctor (yoneda.obj (Xᵢ i))).ι ≫ yoneda.map (rᵢ i))
        (hcanonical i) W ⟨a, trivial⟩
      change (ψᵢ i).IsCanonicalTestMap (CostructuredArrow.mk (yonedaEquiv.symm a))
        (a ≫ rᵢ i) at ht
      rw [ha] at ht
      exact ht
  have hstruct (W : Over S) (a : X.obj.obj.obj (op W)) :
      (r.app (op W) a).left ≫ A.relProjHom = (f.app (op W) a).left := by
    have ht := hr.1 W ⟨a, trivial⟩
    change (r.app (op W) a).left ≫ A.relProjHom =
      (yoneda.preimage (yonedaEquiv.symm a ≫ f)).left at ht
    have he : yoneda.preimage (yonedaEquiv.symm a ≫ f) = f.app (op W) a := by
      apply yoneda.map_injective
      rw [Functor.map_preimage]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    rw [he] at ht
    exact ht
  exact ⟨hgenU, r, hr, space_map_open_proj_base_change S T X f A I Tᵢ Xᵢ g hget
    hcover k fᵢ hcart Aᵢ D r hstruct rᵢ hmap hopen, hmap⟩

end AlgebraicGeometry.AlgebraicSpace
