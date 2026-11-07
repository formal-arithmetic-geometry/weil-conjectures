/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

import Submission.WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSquare
import Submission.WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit
import Submission.WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism
import all Mathlib.Algebra.Homology.Localization

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical module base change under open restriction

Source: Stacks Project, Tags 08FE and 08HY; the local reduction in Tag 08IB.
(blueprint: lem-pc-canonical-module-base-change-open-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom TopCat.Sheaf
  DerivedCategory HomotopyCategory
attribute [local irreducible] Scheme.Modules.tensorPullback

private theorem comparison_conjugate {C : Type*} [Category C]
    {L L0 N N0 : C} (m : L ⟶ N) (n : L0 ⟶ N0)
    (a : L ≅ L0) (b : N ≅ N0) (A : N ≅ N)
    (h : m ≫ b.hom = a.hom ≫ n) :
    (m ≫ A.hom) ≫ (A.symm ≪≫ b).hom = a.hom ≫ n := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact h

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
-- The combined open/affine proof exhausted 400000; check the open argument separately.
/-- Restriction identifies the module base-change arrow with the arrow of the
chosen pullback of the restricted maps. No affine chart is used.
Source: Stacks Project, Tag 08FE, proof; Tag 08HY, counit construction;
Tag 08IB, first proof paragraph; Tag 0D5U, exact extension by zero.
(blueprint: lem-pc-canonical-module-base-change-open-comparison).

Proof:
1. Put U = f inverse image of V and Z = f' inverse image of W. The restricted
square with vertices Z,U,W,V is cartesian: a map to U and W agreeing over V
composes to a cone for the original square, whose unique lift lands in Z.
Identify Z with the chosen pullback of f restricted to V and g restricted from
W to V. Both projections agree under this identification.
2. Apply the pullback restriction comparison to g and direct-image restriction
to f. Exact restriction takes G[0] to H[0], yielding a. Apply direct-image
restriction to f', and identify restriction of g'^*G with the ordinary pullback
of H under the first projection, yielding b. These are isomorphisms.
3. Unpack hc as a left-derived counit epsilon. For a complex K on U, evaluate
epsilon on its termwise extension by zero to X, restrict the result to Z, and
use the projection comparisons to regard it as a counit for the first projection.
Extension by zero is exact and preserves K-flatness: tensoring an extension by
zero with a test complex is extension by zero of the tensor with its restriction,
and both restriction and extension by zero preserve acyclicity. Thus the new
counit is invertible on K-flat representatives and has the left-derived universal
property. Naturality at the extension-by-zero counit j_!(M|U) -> M shows that its
value on M|U agrees with epsilon on M restricted to Z. In particular this holds
for M = G[0]. Compose the value on H[0] with the single-complex identification
to obtain c0 and its comparison predicate (exists_isDerivedModulePullbackComparison).
4. Transpose the derived mate of Tag 08HY under the restricted adjunction.
The open-square identity for underived mates commutes with restriction on
complexes. Localizing and using the derived adjunction equations gives the same
identity for the derived mate. Naturality of the direct-image restriction
comparison then composes this identity with the transported epsilon, giving the
displayed square. No invertibility of the base-change arrow is asserted.
The argument is valid for empty opens and the zero module. -/
theorem exists_canonicalModuleBaseChange_open_comparison
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
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) H c0 ∧
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          (derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H)),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E0 ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
      := by
  classical
  intro U fA gA H E E0 R
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let p := pullback.fst (f ∣_ V) (g.resLE V W hWV)
  let q := pullback.snd (f ∣_ V) (g.resLE V W hWV)
  let c₁ := openPinnedSingleDegreeZeroCounit.{u, w} g' G
  let cV := openPinnedSingleDegreeZeroCounit.{u, w} p H
  have hcV : IsDerivedModulePullbackComparison p H cV :=
    pinned_comparison_isComparison.{u, w} p H
  obtain ⟨α, hα⟩ := modulePullbackComparison_target_automorphism.{u, w}
    g' G c₁ c (pinned_comparison_isComparison.{u, w} g' G) hc
  obtain ⟨aP, bP, hP⟩ :=
    open_pinned_single_degree_zero_square.{u, w} f g g' f' sq V W hWV
  let A := R.mapIso ((schemeDerivedDirectImage f').mapIso
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).mapIso α))
  let aV := aP.app G
  let bV := A.symm ≪≫ bP.app G
  have h := comparison_conjugate _ _ (aP.app G) (bP.app G) A (hP G)
  change (R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
    (schemeDerivedDirectImage f').map c₁) ≫ A.hom) ≫ bV.hom =
    aV.hom ≫ (schemeDerivedBaseChangeMap (f ∣_ V) q (g.resLE V W hWV) p
      pullback.condition E0 ≫ (schemeDerivedDirectImage q).map cV) at h
  have hV : R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
      (schemeDerivedDirectImage f').map c) ≫ bV.hom =
      aV.hom ≫ (schemeDerivedBaseChangeMap (f ∣_ V) q (g.resLE V W hWV) p
        pullback.condition E0 ≫ (schemeDerivedDirectImage q).map cV) := by
    simpa only [hα, A, Functor.map_comp, Functor.mapIso_hom,
      Category.assoc] using h
  exact ⟨cV, hcV, aV, bV, hV⟩

end AlgebraicGeometry
