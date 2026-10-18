/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor

import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Levelwise K-injective towers compute additive functors

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok,
and Derived Categories, Tags 070I, 070Y, 070K
(blueprint: lem-sp-levelwise-kinjective-tower-image).

The index `n : ℕ` denotes the positive level `n + 1`. Tower K-injectivity is
Mathlib's `CochainComplex.IsKInjective` in the abelian functor category, whereas
levelwise K-injectivity applies that predicate separately to each evaluation.
-/

@[expose] public section

set_option autoImplicit false

universe wA wB vA vB uA uB uC vC r uD vD s

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

/-- Apply an additive functor levelwise to a strict tower.
Source: Stacks Tag 0941, combined with Tag 070K
(blueprint: lem-sp-levelwise-kinjective-tower-image). -/
abbrev onStrictTowers {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B] (G : A ⥤ B) :
    (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ B) :=
  (Functor.whiskeringRight ℕᵒᵖ A B).obj G

/-- The canonical complex-level comparison to the recorded total right derived functor.
It is the unit on the homotopy category, transported along `quotientCompQhIso`.
No resolution is chosen anew in this comparison.
Source: Stacks Tags 070Y, 070K and the comparison in Tag 0941
(blueprint: lem-sp-levelwise-kinjective-tower-image). -/
noncomputable def strictTowerDerivedComparison
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (G : A ⥤ B) [G.Additive]
    (h : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).obj X) ⟶
      (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).obj
        (DerivedCategory.Q.obj X) :=
  (DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ B)).inv.app
      ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).obj X) ≫
    (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (.up ℤ)).obj X) ≫
    (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map
      ((DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ A)).hom.app X)

private theorem map_sequence_composite
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    (F : C ⥤ D) {Z : ℕ → C} (f : ∀ n, Z n ⟶ Z (n + 1))
    (i j : ℕ) (hij : i ≤ j) :
    F.map (OfSequence.map f i j hij) =
      OfSequence.map (fun n ↦ F.map (f n)) i j hij := by
  induction i generalizing Z j with
  | zero =>
      induction j generalizing Z with
      | zero => exact F.map_id _
      | succ j hj =>
          cases j with
          | zero => rfl
          | succ j =>
              simp only [OfSequence.map]
              rw [F.map_comp, hj]
  | succ i hi =>
      cases j with
      | zero => omega
      | succ j => exact hi (fun n ↦ f (n + 1)) j (by omega)

private theorem strictTowerComparison_naturality
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (G : A ⥤ B) [G.Additive]
    (h : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (a : X ⟶ Y) :
    DerivedCategory.Q.map ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).map a) ≫
        G.strictTowerDerivedComparison h Y =
      G.strictTowerDerivedComparison h X ≫
        (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map
          (DerivedCategory.Q.map a) := by
  dsimp only [strictTowerDerivedComparison]
  rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    ← Functor.mapHomotopyCategory_map]
  rw [← Category.assoc _ _
    ((G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map _)]
  have hn := (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).naturality
    ((HomotopyCategory.quotient _ _).map a)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, DerivedCategory.quotientCompQhIso_hom_naturality,
    Functor.map_comp]

/-- Levelwise K-injective strict towers compute the total derived levelwise image.

Source: Stacks Tag 0941, lemma-derived-limit-is-ok, evaluation paragraph, combined with
Tags 070I, 070Y and 070K (blueprint: lem-sp-levelwise-kinjective-tower-image).

The commutativity hypotheses say precisely that R and S are sheaves of commutative rings.
The module universes contain each site's object and morphism universes independently.
Sheafification supplies their canonical abelian structures. The datum h is the resolution
construction stipulated in the node's definition of the total derived functor, with
arbitrary quasi-isomorphisms, not necessarily monomorphisms. No exactness of G is assumed.
The last clause is the actual strict tower, with constant term GJ and transition G(s).
Together with invertibility of the canonical comparison it represents the derived image.

Proof plan:
1. Exact evaluation computes cohomology levelwise by
   lem-weil-tower-category-levelwise-abelian. Thus q evaluates to quasi-isomorphisms.
   By lem-weil-tower-evaluation-kinjective, each Q level is K-injective.
2. Both endpoints of each evaluated q are K-injective. Apply
   lem-weil-pbc-kinjective-hom-derived to choose a homotopy inverse separately at each
   level; these inverses need not commute with transitions.
3. Additivity carries the two homotopy equations through G. Therefore each G(q_n)
   is a homotopy equivalence, hence a quasi-isomorphism.
4. Cohomology in the target tower category is levelwise, so the strict image map
   is a quasi-isomorphism and its derived localization is invertible.
5. The unit of def-sfb-right-derived-functor is invertible on Q. Naturality at q
   identifies the comparison at X, followed by the resolution-computation isomorphism,
   with the localized strict image of q. Hence the comparison at X is invertible.
6. The same unit gives naturality for strict maps between levelwise K-injectives.
   Applying G to the strict transition square gives the displayed compatibility.
   If all terms equal J and all successor transitions equal s, applying G gives the
   strict tower with constant term GJ and transitions G(s), as asserted. -/
theorem levelwiseKInjectiveTowerImage
    {SiteC : Type uC} {SiteD : Type uD}
    [Category.{vC} SiteC] [Category.{vD} SiteD]
    {JC : GrothendieckTopology SiteC} {JD : GrothendieckTopology SiteD}
    [HasSheafify JC AddCommGrpCat.{max uC vC r}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    [HasSheafify JD AddCommGrpCat.{max uD vD s}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (R : Sheaf JC RingCat.{max uC vC r}) (S : Sheaf JD RingCat.{max uD vD s})
    (_hRcomm : ∀ (U : SiteCᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hScomm : ∀ (U : SiteDᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{wA}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R)]
    [HasDerivedCategory.{wB}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s, max uD vD s, vD, uD} S)]
    (G : ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R ⥤
      ringedSiteModules.{max uD vD s, max uD vD s, vD, uD} S) [G.Additive]
    (h : ∀ K : CochainComplex
        (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ,
      ∃ (I : CochainComplex
        (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ)
        (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (X : CochainComplex
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ)
    (hX : ∀ n : ℕᵒᵖ, CochainComplex.IsKInjective (X.asFunctor.obj n)) :
    (∀ (Q : CochainComplex
        (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ)
        (q : X ⟶ Q), Q.IsKInjective → QuasiIso q →
      (∀ n : ℕᵒᵖ, CochainComplex.IsKInjective (Q.asFunctor.obj n)) ∧
      (∀ n : ℕᵒᵖ, QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app n))) ∧
      QuasiIso ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).map q) ∧
      (∀ (n m : ℕᵒᵖ) (t : n ⟶ m),
        (G.mapHomologicalComplex (.up ℤ)).map (X.asFunctor.map t) ≫
            (G.mapHomologicalComplex (.up ℤ)).map
              ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app m) =
          (G.mapHomologicalComplex (.up ℤ)).map
              ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app n) ≫
            (G.mapHomologicalComplex (.up ℤ)).map (Q.asFunctor.map t))) ∧
    IsIso (G.strictTowerDerivedComparison h X) ∧
    (∀ (Y : CochainComplex
        (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ),
      (∀ n : ℕᵒᵖ, CochainComplex.IsKInjective (Y.asFunctor.obj n)) → ∀ a : X ⟶ Y,
      DerivedCategory.Q.map ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).map a) ≫
          G.strictTowerDerivedComparison h Y =
        G.strictTowerDerivedComparison h X ≫
          (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map
            (DerivedCategory.Q.map a)) ∧
    (∀ (J : CochainComplex
        (ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ) (e : J ⟶ J),
      J.IsKInjective → X.asFunctor = Functor.ofOpSequence (X := fun _ : ℕ ↦ J) (fun _ : ℕ ↦ e) →
      ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).obj X).asFunctor =
        Functor.ofOpSequence
          (X := fun _ : ℕ ↦ (G.mapHomologicalComplex (.up ℤ)).obj J)
          (fun _ : ℕ ↦ (G.mapHomologicalComplex (.up ℤ)).map e)) := by
  have hres (Q : CochainComplex
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r, max uC vC r, vC, uC} R) ℤ)
      (q : X ⟶ Q) (hQ : Q.IsKInjective) (hq : QuasiIso q) :
      (∀ n : ℕᵒᵖ, CochainComplex.IsKInjective (Q.asFunctor.obj n)) ∧
      (∀ n : ℕᵒᵖ, QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app n))) ∧
      QuasiIso ((G.onStrictTowers.mapHomologicalComplex (.up ℤ)).map q) := by
    have hQn := tower_evaluation_isKInjective _ Q
    have hqn (n : ℕᵒᵖ) : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app n)) := by
      have : CochainComplex.IsKInjective
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj X).obj n) := by
        change CochainComplex.IsKInjective (X.asFunctor.obj n)
        exact hX n
      have : CochainComplex.IsKInjective
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj Q).obj n) := by
        change CochainComplex.IsKInjective (Q.asFunctor.obj n)
        exact hQn n
      have heval : QuasiIso
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app n) :=
        (HomologicalComplex.quasiIso_iff_evaluation q).mp hq n
      obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff _).mp heval
      rw [← he]
      exact (G.mapHomotopyEquiv e).quasiIso_hom
    exact ⟨hQn, hqn,
      (HomologicalComplex.quasiIso_iff_evaluation _).mpr hqn⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q q hQ hq
    obtain ⟨hQn, hqn, hGq⟩ := hres Q q hQ hq
    refine ⟨hQn, hqn, hGq, ?_⟩
    intro n m t
    simpa only [HomologicalComplex.complexOfFunctorsToFunctorToComplex,
      Functor.map_comp] using congrArg
      (fun f ↦ (G.mapHomologicalComplex (.up ℤ)).map f)
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).naturality t)
  · obtain ⟨Q, q, hQ, hq⟩ := h X
    have hGq := (hres Q q hQ hq).2.2
    have := G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h Q
    have hi : IsIso (G.strictTowerDerivedComparison h Q) := by
      dsimp only [strictTowerDerivedComparison]
      infer_instance
    have hn := strictTowerComparison_naturality G h q
    have hr : IsIso
        ((G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map
          (DerivedCategory.Q.map q)) := by infer_instance
    have hc : IsIso
        (G.strictTowerDerivedComparison h X ≫
          (G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map
            (DerivedCategory.Q.map q)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((G.onStrictTowers.rightDerivedFunctorOfQuasiIsoResolutions h).map
        (DerivedCategory.Q.map q))
  · intro Y _ a
    exact strictTowerComparison_naturality G h a
  · intro J e _ he
    change X.asFunctor ⋙ G.mapHomologicalComplex (.up ℤ) = _
    rw [he]
    refine Functor.ext (fun n ↦ rfl) ?_
    intro n m t
    simpa only [Functor.ofOpSequence, Functor.ofSequence, Functor.leftOp, Functor.op,
      Functor.comp_map, Quiver.Hom.unop_op, eqToHom_refl,
      Category.id_comp, Category.comp_id] using
      congrArg Quiver.Hom.unop
        (map_sequence_composite (G.mapHomologicalComplex (.up ℤ)).op
          (fun _ : ℕ ↦ e.op) m.unop n.unop (leOfHom t.unop))

end CategoryTheory.Functor
