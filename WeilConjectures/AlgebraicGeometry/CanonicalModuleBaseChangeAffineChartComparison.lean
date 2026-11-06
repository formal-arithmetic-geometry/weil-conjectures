/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

import WeilConjectures.AlgebraicGeometry.DerivedModulePullbackComparison
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSquare
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit
import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism
import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparison
import all Mathlib.Algebra.Homology.Localization
import Mathlib.Tactic.Trace

/-! # The canonical module base-change arrow in affine charts

Source: Stacks Project, Tags 08IB (local reduction), 08HY (the canonical mate),
and 08FE (restriction of derived direct image).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Composing two commuting squares composes their endpoint isomorphisms. -/
private theorem comparison_comp
    {C : Type*} [Category C] {A B A' B' A'' B'' : C}
    (x : A ⟶ B) (y : A' ⟶ B') (z : A'' ⟶ B'')
    (a : A ≅ A') (b : B ≅ B') (a' : A' ≅ A'') (b' : B' ≅ B'')
    (h : x ≫ b.hom = a.hom ≫ y) (h' : y ≫ b'.hom = a'.hom ≫ z) :
    x ≫ (b ≪≫ b').hom = (a ≪≫ a').hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]

private theorem comparison_conjugate {C : Type*} [Category C]
    {L L0 N N0 : C} (m : L ⟶ N) (n : L0 ⟶ N0)
    (a : L ≅ L0) (b : N ≅ N0) (A : N ≅ N) (B : N0 ≅ N0)
    (h : m ≫ b.hom = a.hom ≫ n) :
    (m ≫ A.hom) ≫ (A.symm ≪≫ b ≪≫ B).hom = a.hom ≫ (n ≫ B.hom) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc]

private theorem pinned_comparison_isComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) :
    IsDerivedModulePullbackComparison k M (openPinnedSingleDegreeZeroCounit k M) := by
  classical
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  refine ⟨ε, ?_, rfl⟩
  exact Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k

set_option maxHeartbeats 400000 in
set_option diagnostics true in
-- The replacement proof exhausted 200000 heartbeats in the remote check (12s).
/-- Restriction and affine charts identify the canonical *arrow*, without asserting
that it is invertible. Both the restricted scheme and its module are explicit.
Source: Stacks Project, Tag 08IB, first paragraph of the proof; Tag 08HY and Tag 08FE.
(blueprint: lem-pc-canonical-module-base-change-affine-chart-comparison).

Proof: use the pinned degree-zero open square on V and W, then conjugate its
target isomorphisms to the chosen comparisons c and cV using their target
automorphisms. This gives endpoint isomorphisms aV and bV with a commuting square.
Apply exists_canonicalModuleBaseChange_iso_comparison to that chosen cartesian
square and the spectrum charts V.isoSpec and W.isoSpec. Its module is exactly
H = G restricted to U. It gives c0, endpoint isomorphisms a0 and b0, and a second
commuting square. The resulting chart maps are definitionally the displayed fA
and gA. Take a = aV followed by a0 and b = bV followed by b0. Associativity
composes the two square equations, giving the required equality. The transported
comparison c0 satisfies the comparison predicate supplied by the coordinate step.
Neither step assumes flatness, quasi-coherence or invertibility of base change.
Both apply to empty opens and the zero module. -/
theorem exists_canonicalModuleBaseChange_affineChart_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    (V : S.affineOpens) (W : S'.affineOpens) (hWV : W.1 ≤ g ⁻¹ᵁ V.1) :
    let U := f ⁻¹ᵁ V.1
    let fA := (f ∣_ V.1) ≫ V.2.isoSpec.hom
    let gA := W.2.isoSpec.inv ≫ g.resLE V.1 W.1 hWV ≫ V.2.isoSpec.hom
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
    let R := (schemeOpenRestriction S' W.1).mapDerivedCategory
    let T := schemeDerivedDirectImage W.2.isoSpec.inv
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) H c0 ∧
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0)),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H))),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫ T.map
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E0 ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
      := by
  classical
  intro U fA gA H E E0 R T
  trace "BZ864: introduced lets"
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  trace "BZ864: normalized aliases"
  obtain ⟨cV, hcV⟩ := exists_isDerivedModulePullbackComparison.{u, w}
    (pullback.fst (f ∣_ V.1) (g.resLE V.1 W.1 hWV)) H
  trace "BZ864: chose comparison"
  let p := pullback.fst (f ∣_ V.1) (g.resLE V.1 W.1 hWV)
  let q := pullback.snd (f ∣_ V.1) (g.resLE V.1 W.1 hWV)
  let c₁ := openPinnedSingleDegreeZeroCounit.{u, w} g' G
  let c₂ := openPinnedSingleDegreeZeroCounit.{u, w} p H
  obtain ⟨α, hα⟩ := modulePullbackComparison_target_automorphism.{u, w}
    g' G c₁ c (pinned_comparison_isComparison g' G) hc
  obtain ⟨γ, hγ⟩ := modulePullbackComparison_target_automorphism.{u, w}
    p H c₂ cV (pinned_comparison_isComparison p H) hcV
  trace "BZ864: chose automorphisms"
  obtain ⟨aP, bP, hP⟩ :=
    open_pinned_single_degree_zero_square.{u, w} f g g' f' sq V.1 W.1 hWV
  trace "BZ864: obtained square"
  let A := R.mapIso ((schemeDerivedDirectImage f').mapIso
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).mapIso α))
  let B := (schemeDerivedDirectImage q).mapIso
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback (f ∣_ V.1)
        (g.resLE V.1 W.1 hWV)).toRingedSpace)) 0).mapIso γ)
  let aV := aP.app G
  let bV := A.symm ≪≫ bP.app G ≪≫ B
  trace "BZ864: defined endpoints"
  have h := comparison_conjugate _ _ (aP.app G) (bP.app G) A B (hP G)
  trace "BZ864: conjugated square"
  change (R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
    (schemeDerivedDirectImage f').map c₁) ≫ A.hom) ≫ bV.hom =
    aV.hom ≫ ((schemeDerivedBaseChangeMap (f ∣_ V.1) q (g.resLE V.1 W.1 hWV) p
      pullback.condition E0 ≫ (schemeDerivedDirectImage q).map c₂) ≫ B.hom) at h
  trace "BZ864: changed square"
  have hV : R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
      (schemeDerivedDirectImage f').map c) ≫ bV.hom =
      aV.hom ≫ (schemeDerivedBaseChangeMap (f ∣_ V.1) q (g.resLE V.1 W.1 hWV) p
        pullback.condition E0 ≫ (schemeDerivedDirectImage q).map cV) := by
    simpa only [hα, hγ, A, B, Functor.map_comp, Functor.mapIso_hom,
      Category.assoc] using h
  trace "BZ864: normalized square"
  have hi := exists_canonicalModuleBaseChange_iso_comparison.{u, w}
    (f ∣_ V.1) (g.resLE V.1 W.1 hWV)
    (pullback.fst (f ∣_ V.1) (g.resLE V.1 W.1 hWV))
    (pullback.snd (f ∣_ V.1) (g.resLE V.1 W.1 hWV))
    (IsPullback.of_hasPullback _ _) H cV hcV V.2.isoSpec W.2.isoSpec
  trace "BZ864: obtained coordinate comparison"
  rcases hi with ⟨c0, h⟩
  rcases h with ⟨hc0, h⟩
  rcases h with ⟨a0, h⟩
  rcases h with ⟨b0, h0⟩
  refine ⟨c0, ?_⟩
  refine ⟨hc0, ?_⟩
  refine ⟨aV ≪≫ a0, ?_⟩
  refine ⟨bV ≪≫ b0, ?_⟩
  trace "BZ864: closing composite"
  exact comparison_comp _ _ _ aV bV a0 b0 hV h0

end AlgebraicGeometry
