/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
import Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishingAux
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.Sites.CechCriterion
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Affine vanishing for comparison pullbacks of injective abelian sheaves

Source: Stacks Project, Pro-etale Cohomology, Tag 099U, `lemma-affine-vanishing`
(blueprint: lem-cbc-abelian-affine-comparison-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

theorem affineProEt_cechNerve (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ i, proAffineEtale (U i).left.hom) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    proAffineEtale (Presheaf.cechNerveObj U y).left.hom := by
  let T : Y.AffineProEt := .ofEtale (𝟙 Y)
  have hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun W ↦ MorphismProperty.Over.homMk W.hom) (by
      intro W f
      apply MorphismProperty.Over.Hom.ext
      have hf : f.left ≫ 𝟙 Y = W.hom := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans hf)
  let : HasTerminal Y.AffineProEt := hT.hasTerminal
  have : PreservesLimit (Functor.empty Y.AffineProEt)
      (Scheme.AffineProEt.toProEt Y) := by
    apply preservesTerminal_of_iso
    exact (Scheme.AffineProEt.toProEt Y).mapIso
      (terminalIsTerminal.uniqueUpToIso hT) ≪≫
      (MorphismProperty.Over.mkIdTerminal _ Y).uniqueUpToIso terminalIsTerminal
  have : PreservesLimitsOfShape (Discrete PEmpty) (Scheme.AffineProEt.toProEt Y) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have : PreservesFiniteLimits (Scheme.AffineProEt.toProEt Y) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  have : HasFiniteLimits Y.AffineProEt := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let X : Y.AffineProEt := .mk V.hom hV
  let W (i : Fin n) : Over X :=
    Over.mk (MorphismProperty.Over.homMk (U i).hom.left (U i).hom.w :
      Scheme.AffineProEt.mk (U i).left.hom (hU i) ⟶ X)
  let G := Over.post (Scheme.AffineProEt.toProEt Y) (X := X)
  let e := PreservesProduct.iso G (fun j : Fin (k + 1) ↦ W (y j))
  have h : proAffineEtale (G.obj (∏ᶜ fun j : Fin (k + 1) ↦ W (y j))).left.hom :=
    (∏ᶜ fun j : Fin (k + 1) ↦ W (y j)).left.prop
  have he : (fun j : Fin (k + 1) ↦ G.obj (W (y j))) =
      (fun j : Fin (k + 1) ↦ U (y j)) := by rfl
  rw [he] at e
  have hw : e.inv.left.left ≫
      (G.obj (∏ᶜ fun j : Fin (k + 1) ↦ W (y j))).left.hom =
        (Presheaf.cechNerveObj U y).left.hom := by simp
  rw [← hw, proAffineEtale.cancel_left_of_respectsIso]
  exact h

theorem affineProEt_finite_refinement (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    (R : Sieve V) (hR : R ∈ Scheme.ProEt.topology Y V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, proAffineEtale (U i).left.hom) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
        Scheme.ProEt.topology Y V := by
  classical
  let X : Y.AffineProEt := .mk V.hom hV
  let F := Scheme.AffineProEt.toProEt Y
  have hr : R.functorPullback F (X := X) ∈ Scheme.AffineProEt.topology Y X :=
    F.cover_lift _ _ hR
  obtain ⟨ι, hι, W, f, hf, hsurj⟩ :=
    Scheme.AffineProEt.exists_finite_jointly_surjective_of_mem_topology hr
  let := hι
  let := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let U (i : Fin (Fintype.card ι)) : Over V := Over.mk (F.map (f (e i)))
  refine ⟨Fintype.card ι, U, fun i ↦ (W (e i)).prop, fun i ↦ hf (e i), ?_⟩
  apply Precoverage.generate_mem_toGrothendieck
  change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
    Scheme.ProEt.precoverage Y V
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  let D : PreZeroHypercover V.left :=
    ⟨Fin (Fintype.card ι), fun i ↦ (W (e i)).left, fun i ↦ (f (e i)).left⟩
  have hs : ∀ x : V.left, ∃ i, x ∈ Set.range (D.f i) := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨e.symm i, ?_⟩
    change x ∈ Set.range (f (e (e.symm i))).left
    rw [e.apply_symm_apply]
    exact ⟨y, hy⟩
  have : ∀ i, IsAffine (D.X i) := fun i ↦ (W (e i)).prop.isAffine
  have : IsAffine V.left := hV.isAffine
  have hD : QuasiCompactCover D :=
    ⟨fun {O} hO ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i ↦ (D.f i).isSpectralMap) (fun x _ ↦ hs x) O.2 hO.isCompact⟩
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD,
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2
      ⟨hs, fun i ↦ by
        change WeaklyEtale (f (e i)).left
        infer_instance⟩⟩

/-- On an affine scheme, the comparison inverse image of any injective abelian etale
sheaf has zero positive pro-etale cohomology. No restriction on coefficients is imposed.
Source: Stacks Project, Tag 099U, `lemma-affine-vanishing`
(blueprint: lem-cbc-abelian-affine-comparison-vanishing).

Proof:
1. The comparison section formula (lem-cbc-comparison-pullback-sections) identifies
   sections of F = nu⁻¹J with etale sections of the inverse image of J. Naturality for
   addition, zero and negation makes this an identification of abelian groups, compatible
   with all restriction maps. On etale objects it identifies F with J.
2. Degree-zero continuity (lem-weil-pbc-etale-cohomology-limit-of-schemes) identifies
   sections on an affine directed limit with the colimit of sections at its stages.
   All affine objects are qcqs (lem-weil-pbc-affine-scheme-qcqs).
3. Exact filtered colimits of abelian groups commute with finite products, kernels,
   images and cohomology. Applied degreewise to the site Cech complex, the section
   comparisons commute with every omitted-factor restriction and hence the differential.
4. The affine ind-etale basis and ind-etale stability provide finite cofinal covers
   closed under intersections, verifying the first two hypotheses of the site Cech
   vanishing criterion (lem-weil-pbc-site-cech-vanishing-criterion).
5. Present each member of such a finite cover as a directed limit of affine etale
   objects. Replace the finitely many indices by their product using directed cofinal
   reindexing. Each stage family is surjective, since the limit family is. Fibre products
   commute with limits (lem-kun-fibre-product-limits); the affine limits exist by
   lem-weil-pbc-limit-affine-transition. The empty cover has zero Cech complex.
6. Steps 2 and 3 reduce positive Cech vanishing to finite affine etale covers of a
   basis object, without asserting injectivity on a different etale site.
7. Present that basis object as a directed limit of affine etale Y-schemes. Descend the
   finite cover by lem-weil-pbc-affine-etale-site-colimit; descend its target isomorphism
   and inverse to fix the target at a common later stage. Etale composition, cancellation
   and base change put all stage intersections on the original etale site. The tail is
   cofinal, and its intersections have the required affine limits.
8. Apply steps 2 and 3 again, including naturality for face maps. At each stage step 1
   identifies the entire Cech complex with that for J on Y_et. Injectivity of J on this
   fixed site gives positive Cech vanishing by lem-weil-pbc-injective-sheaf-cech-acyclic.
9. The site Cech criterion now gives positive cohomology vanishing on every basis
   object. The identity of affine Y is ind-etale and belongs to the basis; take it as
   the object. This includes empty Y, for which the empty-cover complex is zero.

Mathlib's H is the Ext encoding of right derived global sections. Its result is a type,
so vanishing is expressed by Subsingleton. HasExt.standard fixes a model without an
additional hypothesis. Natural degrees q > 0 are exactly the positive integer degrees.
-/
theorem subsingleton_cohomology_comparisonUpperStar_obj_of_injective_of_isAffine
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (@Sheaf.H _ _ _
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J) _ (HasExt.standard _) q) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let : HasExt (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) :=
    HasExt.standard _
  let B : Y.ProEt → Prop := fun V ↦ proAffineEtale V.hom
  let T : Y.ProEt := .mk (𝟙 Y)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply Sheaf.subsingleton_H_succ_of_exactAt_cechComplex
    (J := Scheme.ProEt.topology Y)
    (F := (comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J) (q := n) hT B
    (proAffineEtale.of_isAffine (𝟙 Y))
  · intro V hV R hR
    obtain ⟨m, U, hU, hR, hcover⟩ := affineProEt_finite_refinement Y V hV R hR
    exact ⟨m, U, affineProEt_cechNerve Y V hV U hU, hR, hcover⟩
  · intro V hV m U hU hcover q
    exact exactAt_cechComplex_comparisonUpperStar_of_injective Y J V hV U hU hcover q

end AlgebraicGeometry.ProEtale
