/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import Sheaf.AlgebraicGeometry.AffineComparisonEtaleCechPresentation
import Sheaf.AlgebraicGeometry.AffineComparisonCechSystemSections
import Sheaf.CategoryTheory.OrderedCechUliftComparison

/-!
# Descent of finite affine comparison Čech cocycles

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions in condition (3).
(blueprint: lem-cbc-affine-comparison-cech-cocycle-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- A comparison Čech cocycle with arbitrary étale sheaf coefficients comes from an
étale Čech cocycle by a morphism of complexes for a finite étale covering.
No injectivity, exactness or primitive is asserted.
Source: Stacks Project, Tag 099U, condition (3), the two finite Čech limit reductions;
Tags 099S and 099T for section continuity and the unit, and Tags 01ZM, 01ZN, 07RP
for finite étale descent.
(blueprint: lem-cbc-affine-comparison-cech-cocycle-descent).

Proof:
1. Use the singleton-product isomorphism to extract affine ind-étale hypotheses
   for the individual family members. Replace their finite disjoint union by an
   affine scheme and factor the family through a single surjection. Present this
   surjection by affine étale Y-schemes, covering at each stage. Descend the finite
   affine open cover of its source to one stage and pull it back along the
   over-category of that stage. Its composites with the surjection give covering
   presentations of the original family, with its original finite indexing.
2. The wide-pullback universal property constructs every repeated intersection,
   its transition maps and its cone legs. Base and member limit properties prove
   that each such cone is a scheme limit. Projection equations prove compatibility
   with every face map, and all stage intersections are affine.
3. Comparison section continuity identifies sections on every intersection with
   the filtered colimit of stage sections. The comparison unit identifies stage
   sections with those of J. Its naturality and the face equations give complex
   maps from every stage to the original ordered complex.
4. Choose representatives of the finitely many degree q+1 components at a common
   stage. Their differential has zero image because c is a cocycle. Filtered
   colimit eventual equality and a finite wide span give one further transition
   killing all degree q+2 differential components. Transporting the cochain gives
   a stage cocycle with image c.
5. Identify categorical product cochains with dependent-function cochains and
   reindex by ULift. The product projection formulas identify the differentials,
   so the resulting complex isomorphism transports the stage cocycle and gives
   the required map φ and its equation. Empty families and empty schemes use
   the same finite-cover and product constructions; no nonemptiness is assumed. -/
theorem exists_etale_cech_cocycle_lift
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      proAffineEtale (Presheaf.cechNerveObj U y).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) (q : ℕ)
    (c : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).X (q + 1))
    (hc : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).d (q + 1) (q + 2) c = 0) :
    ∃ (W : Y.Etale) (T : ULift.{u + 1} (Fin n) → Y.Etale)
      (f : ∀ i, T i ⟶ W),
      Sieve.ofArrows T f ∈ Y.smallEtaleTopology W ∧
      ∃ (φ : (cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj) ⟶
        (Presheaf.cechComplex U).obj
          ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj)
        (c' : ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).X (q + 1)),
        ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).d (q + 1) (q + 2) c' = 0 ∧
          φ.f (q + 1) c' = c := by
  obtain ⟨I, _, _, S, hS⟩ := exists_affine_etale_cech_system Y V hV U hU hcover
  obtain ⟨i, x, hx, hxc⟩ := S.exists_cocycle_lift J hS (q + 1) c hc
  let e := Presheaf.orderedCechUliftIso (fun a ↦ Over.mk (S.f i a)) J.obj
  refine ⟨S.W i, (fun a ↦ S.T i a.down), (fun a ↦ S.f i a.down), ?_,
    e.hom ≫ S.toOriginal J i, e.inv.f (q + 1) x, ?_, ?_⟩
  · have he : Sieve.ofArrows (fun a : ULift.{u + 1} (Fin n) ↦ S.T i a.down)
        (fun a ↦ S.f i a.down) = Sieve.ofArrows (S.T i) (S.f i) := by
      apply congrArg Sieve.generate
      apply le_antisymm
      · rintro Z g ⟨a⟩
        exact ⟨a.down⟩
      · rintro Z g ⟨a⟩
        exact ⟨ULift.up a⟩
    rw [he]
    exact S.covering i
  · have h := ConcreteCategory.congr_hom (e.inv.comm (q + 1) (q + 2)) x
    change (S.stageComplex J i).d (q + 1) (q + 2) x = 0 at hx
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx, map_zero] at h
    exact h
  · change (S.toOriginal J i).f (q + 1) (e.hom.f (q + 1) (e.inv.f (q + 1) x)) = c
    have he := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom e.inv_hom_id (q + 1)) x
    change e.hom.f (q + 1) (e.inv.f (q + 1) x) = x at he
    rw [he]
    exact hxc

end AlgebraicGeometry.ProEtale
