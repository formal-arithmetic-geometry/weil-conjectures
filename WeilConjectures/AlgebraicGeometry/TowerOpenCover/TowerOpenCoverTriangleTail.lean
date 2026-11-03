/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverEvaluationArrows
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! Compact-support and finite-level transport for the tower open-cover triangle.
Source: latest blueprint, sec-smooth-purity/sk-prop-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-triangle-tail).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- Apply compact support and every exact coefficient evaluation to the core
open-cover triangle, with the normalized finite arrows displayed in the parent.
(blueprint: lem-dla1-tower-open-cover-triangle-tail).

Source: latest blueprint, tower-geometric Gluing and Levels paragraphs.

The input is a family of boundaries whose specified triangles are distinguished.
No cover or naturality hypotheses are needed for this transport step.

Proof: exact open extension and the right-derived proper direct image form a
triangulated compact-support functor on bounded-below objects. Exact evaluation is
triangulated and the normalized pull/open comparisons identify the first two maps
with `finiteAlpha` and the finite counits; the shift comparison identifies the
third map.
-/
theorem tower_open_cover_tail {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (delta : ∀ M : SpTowerShriek.D l E X, M ⟶
      ((support l E b o jW).obj M)⟦(1 : ℤ)⟧)
    (htriangle : ∀ M : SpTowerShriek.D l E X,
      Triangle.mk (first l E b o aU aV jU jV jW wU wV M)
        (second l E b o jU jV M) (delta M) ∈ distTriang (SpTowerShriek.D l E X)) :
    (∀ {Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
        (M : DerivedCategory.Plus (SpTowerShriek.S l E X)),
        (SpTowerShriek.F l E b o c).mapTriangle.obj
          (Triangle.mk (first l E b o aU aV jU jV jW wU wV M.obj)
            (second l E b o jU jV M.obj) (delta M.obj)) ∈
          distTriang (SpTowerShriek.D l E Y)) ∧
      (∀ (M : SpTowerShriek.D l E X) (n : ℕ),
        ∃ d : (SpTowerShriek.Ev l E X n).obj M ⟶
          ((finiteSupport l E b jW n).obj ((SpTowerShriek.Ev l E X n).obj M))⟦(1 : ℤ)⟧,
        ∃ e : (SpTowerShriek.Ev l E X n).mapTriangle.obj
            (Triangle.mk (first l E b o aU aV jU jV jW wU wV M)
              (second l E b o jU jV M) (delta M)) ≅
          Triangle.mk
            (biprod.lift
              (finiteAlpha l E b aU jU jW wU n ((SpTowerShriek.Ev l E X n).obj M))
              (-finiteAlpha l E b aV jV jW wV n ((SpTowerShriek.Ev l E X n).obj M)))
            (biprod.desc
              ((finiteAdjunction l E b jU n).counit.app
                ((SpTowerShriek.Ev l E X n).obj M))
              ((finiteAdjunction l E b jV n).counit.app
                ((SpTowerShriek.Ev l E X n).obj M))) d,
          e.hom.hom₁ = (supportEvaluation l E b o jW n).hom.app M ∧
          e.hom.hom₂ = biprod.lift
            ((SpTowerShriek.Ev l E X n).map biprod.fst ≫
              (supportEvaluation l E b o jU n).hom.app M)
            ((SpTowerShriek.Ev l E X n).map biprod.snd ≫
              (supportEvaluation l E b o jV n).hom.app M) ∧
          e.hom.hom₃ = 𝟙 _) := by
  constructor
  · intro Y f _ _ _ c M
    let : Abelian.HasKInjectiveResolutions (SpTowerShriek.S l E c.Z) := b.kinjective c.Z
    have : (SpTowerShriek.F l E b o c).IsTriangulated := by
      change ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor).IsTriangulated
      infer_instance
    exact Functor.map_distinguished _ _ (htriangle M.obj)
  · intro M n
    let F := SpTowerShriek.Ev l E X n
    let p := (supportEvaluation l E b o jW n).app M
    let qU := (supportEvaluation l E b o jU n).app M
    let qV := (supportEvaluation l E b o jV n).app M
    have (A B : SpTowerShriek.D l E X) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    let q₀ := F.mapBiprod ((support l E b o jU).obj M)
      ((support l E b o jV).obj M)
    let q := q₀ ≪≫ biprod.mapIso qU qV
    let T := F.mapTriangle.obj
      (Triangle.mk (first l E b o aU aV jU jV jW wU wV M)
        (second l E b o jU jV M) (delta M))
    let d := T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map p.hom
    obtain ⟨hU, hcU⟩ := tower_open_cover_evaluation_arrows l E b o aU jU jW wU M n
    obtain ⟨hV, hcV⟩ := tower_open_cover_evaluation_arrows l E b o aV jV jW wV M n
    have hfirst : T.mor₁ ≫ q.hom = p.hom ≫ biprod.lift
        (finiteAlpha l E b aU jU jW wU n (F.obj M))
        (-finiteAlpha l E b aV jV jW wV n (F.obj M)) := by
      change F.map (first l E b o aU aV jU jV jW wU wV M) ≫ q.hom = _
      dsimp only [q, Iso.trans_hom, q₀]
      rw [← Category.assoc, first, biprod.map_lift_mapBiprod]
      apply biprod.hom_ext
      · simp only [biprod.mapIso_hom, Category.assoc, biprod.map_fst,
          biprod.lift_fst_assoc]
        erw [biprod.lift_fst]
        simpa only [qU, p, F, Iso.app_hom, support] using hU
      · simp only [biprod.mapIso_hom, Category.assoc, biprod.map_snd,
          biprod.lift_snd_assoc]
        erw [biprod.lift_snd]
        simpa only [qV, p, F, Iso.app_hom, support, Functor.map_neg,
          Preadditive.neg_comp, Preadditive.comp_neg] using congrArg Neg.neg hV
    have hsecond : T.mor₂ ≫ (Iso.refl (F.obj M)).hom = q.hom ≫ biprod.desc
        ((finiteAdjunction l E b jU n).counit.app (F.obj M))
        ((finiteAdjunction l E b jV n).counit.app (F.obj M)) := by
      change F.map (second l E b o jU jV M) ≫ 𝟙 _ = _
      simp only [Category.comp_id]
      apply (cancel_epi q₀.inv).1
      dsimp only [q, Iso.trans_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      dsimp only [q₀]
      rw [second, biprod.mapBiprod_inv_map_desc]
      apply biprod.hom_ext'
      · simpa only [qU, F, Iso.app_hom, support, biprod.mapIso_hom, Category.assoc,
          biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc] using hcU
      · simpa only [qV, F, Iso.app_hom, support, biprod.mapIso_hom, Category.assoc,
          biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc] using hcV
    let e : T ≅ Triangle.mk
        (biprod.lift (finiteAlpha l E b aU jU jW wU n (F.obj M))
          (-finiteAlpha l E b aV jV jW wV n (F.obj M)))
        (biprod.desc ((finiteAdjunction l E b jU n).counit.app (F.obj M))
          ((finiteAdjunction l E b jV n).counit.app (F.obj M))) d :=
      Triangle.isoMk _ _ p q (Iso.refl (F.obj M)) hfirst hsecond
        (by
          change T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map p.hom = 𝟙 _ ≫ d
          rw [Category.id_comp])
    refine ⟨d, e, rfl, ?_, rfl⟩
    dsimp only [e, Triangle.isoMk, q, Iso.trans_hom, biprod.mapIso_hom, q₀]
    apply biprod.hom_ext <;>
      simp [qU, qV, F, Category.assoc]

end AlgebraicGeometry.ProEtale.TowerOpenCover
