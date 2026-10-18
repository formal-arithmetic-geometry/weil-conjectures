## What changed

Proved `CategoryTheory.filteredHomologyCouple_quotient_pages` with its exact
original signature. Normalized epic tower projections are cokernels of the
boundary inclusions. Uniqueness of cokernels supplies the comparison isomorphisms;
epic cancellation proves their base normalization and differential compatibility.
The latter calculation uses the existing simultaneous representative cover and
the recorded representative differential formula.

Restored `CategoryTheory.filteredHomology_tower_differential` in its unclaimed
module with exactly its recorded statement and one named `sorry`. That declaration
was still inside a synchronization rollback comment. This restores the missing
interface; its proof remains an obligation. No definition or target changes.

Change record: `coord/changes/filtered-homology-quotient-pages-restore-differential.md`.
Both node statements are unchanged. No new node is introduced.

Validation: the exact fallback payload passed the required dry run as
`0681c77bf1` (nothing pushed). Both files compile and preflight accepts the
named remaining obligation. The existing private transport helper is preserved;
all delivered theorem signatures agree with their recorded statements.

## Proved and sorry left

Closed: `CategoryTheory.filteredHomologyCouple_quotient_pages`, node
`lem-sp-filtered-homology-couple-quotient-pages` (one original hole).

Added/restored as the only delivered hole:
`CategoryTheory.filteredHomology_tower_differential`, node
`lem-sp-filtered-homology-tower-differential` (one hole). Its statement is strictly
part of the argument: it computes the canonical differential on simultaneous
representatives and asserts neither quotient isomorphisms nor their base equation.
The delivered main proof combines it with the quotient presentation by genuine
cokernel uniqueness and epic cancellation. This is a decomposition, with zero net
holes closed. There is no `sorry` in a definition, private helper or partial proof.

What this remaining theorem needs: the published concrete filtered homology couple
and E isomorphism are still hollow, so their D objects and maps do not reduce to
filtration homology. F8 holds that repair. The public forward representative theorem
is also absent; A6 holds it. A full proof of the differential formula, including
the forward calculation and a direct finite-stage cycle-factorization induction,
compiled in scratch against an explicit concrete construction. Its axiom probe
shows only propext, Classical.choice and Quot.sound. Scratch code is outside the
delivery. The intended proof is explained completely in the existing docstring
and node. Neither independently held dependency is changed by this delivery.

The imported `CategoryTheory.filteredHomology_tower_quotients` is an existing
separate obligation; this delivery adds no hole there.

## No longer needed

Removed unused proof-only imports from the assigned module:
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
`Sheaf.CategoryTheory.ExactCouple`. Their APIs are already publicly supplied by
the statement dependencies and quotient presentation.

The deferred differential module needs only its three public statement imports.
Its former proof-only imports
`Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives`,
`Sheaf.CategoryTheory.DerivedCoupleExact` and
`Sheaf.CategoryTheory.FiniteCycleFormula`, and import-all of
`Sheaf.CategoryTheory.FiniteCycleDerivedComparison`, are omitted from this interface
restoration. No node is pruned: those nodes remain in the deferred proof plan, and
all main-node dependencies are used. No module is removed from the target closure.
The unit's realized lists are empty; no unit route is bypassed.

A static import-graph comparison confirms no modules leave the full
`TargetsCheck` closure. The assigned module's own closure loses the retired
`Sheaf.CategoryTheory.FiniteCycleDerivedComparison` wrapper and its upstream
comparison module, but other target consumers still import them.

## Where the brief, the DAG or earlier work was wrong

The brief says every dependency has an available declaration. The shared source
still comments out the public forward and differential theorems after upstream
synchronization. The older return entries confirm the causes: the assigned proof
lost `filteredHomology_tower_differential`, and that dependency lost the private
`BigradedExactCouple.comparisonLift`. Import-all must name its actual defining
module, `WeilConjectures.CategoryTheory.FiniteCycleDerivedComparison`, rather than
the retired Sheaf re-export. The old `ofShifted_g` constant is also unavailable.

The compile server independently confirms the two hollow concrete definitions
and missing public representative theorem. The separately held definition repair
is necessary before the full representative proof can be checked against the
actual library. The full and inlined representative calculations were both
checked against an explicit scratch model; that is not a claim that they compile
against the currently published hollow definitions.

Read the local Stacks source `literature/stacks-project/homology.tex`, Tags 011R
and 012K. Checked zero complexes, zero differential, negative filtration indices,
positions outside finite support, and `s=0`. The bidegree is `(s+1,-s)`, with total
degree increasing by one. Representatives are constructed as image factorizations,
so epic cancellation assumes no projectivity of test objects. Mathlib searches
supply cokernel uniqueness and `ShortComplex.Exact.gIsCokernel`; no ready theorem
identifies this concrete tower with these filtered quotients.

Also checked `WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex`:
it constructs another exact-couple API and proves stable-page convergence,
but supplies no identification of all pages with these representative
cycle-boundary quotients. Replacing the couple framework would still leave the
same comparison obligation, so it does not shorten this argument.

Prepared replacement proof for the remaining differential obligation (not part of
the compiled Lean payload): the module below was checked after substituting the
explicit scratch concrete couple and its initial E isomorphism, and using the
proved scratch forward representative calculation. Its axiom check then uses only
the three allowed axioms. Apply this candidate after the canonical definitions
and the public forward representative theorem have been restored; it does not
compile against the currently published hollow definitions. This preserves the
actual formal argument, including the direct finite-cycle factorization, rather
than asking the next worker to reconstruct it from the prose plan. When applying
this candidate, replace differential-node proof step 4 by the finite-stage
induction below and remove its direct `lem-sp-finite-cycle-formula` dependency;
that is a future route update, not a pruning claimed by this interface delivery.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2, T2
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
import Sheaf.CategoryTheory.DerivedCoupleExact
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.FiniteCycleDerivedComparison

/-! # Representative comparisons with the canonical exact-couple tower

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- The finite-stage induction used by the upstream `g_factors_limitCycles` proof.
Keep the stronger induction invariant that the projected class is killed by page f. -/
private theorem initialG_factors_tower_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q) := by
  let T := X.cycleBoundaryTower
  have hfinite : ∀ r : ℕ, ∃ a : X.D p q ⟶ (T.Z r p q : C),
      a ≫ (T.Z r p q).arrow = X.initialG p q ∧
      a ≫ T.projection r p q ≫ (X.pageCouple r).f p q = 0 := by
    intro r
    induction r with
    | zero =>
      have hfac : (T.Z 0 p q).Factors (X.initialG p q) := by
        rw [T.Z_zero]
        exact Subobject.top_factors _
      refine ⟨(T.Z 0 p q).factorThru _ hfac, by simp, ?_⟩
      rw [T.projection_zero, ← Category.assoc, Subobject.factorThru_arrow]
      change X.initialG p q ≫ X.f p q = 0
      rw [BigradedExactCouple.initialG, Category.assoc,
        ← eqToHom_naturality (fun pq : ℤ × ℤ ↦ X.f pq.1 pq.2)
          (show (p + (0 : ℕ), q - (0 : ℕ)) = (p, q) by ext <;> simp),
        ← Category.assoc, X.f_g_zero, zero_comp]
    | succ r ih =>
      obtain ⟨a, ha, hf⟩ := ih
      let P := (Subobject.pullback (T.projection r p q)).obj
        (kernelSubobject ((X.pageCouple r).d p q))
      have hpa : P.Factors a := by
        apply pullback_factors
        apply kernelSubobject_factors
        simpa only [BigradedExactCouple.d, Category.assoc, zero_comp] using
          congrArg (fun z ↦ z ≫ (X.pageCouple r).g (p + 2) (q - 1)) hf
      have hfac : (T.Z (r + 1) p q).Factors (X.initialG p q) := by
        rw [T.Z_succ, Subobject.exists_obj_eq_imageSubobject]
        rw [← ha, ← P.factorThru_arrow a hpa, Category.assoc]
        exact imageSubobject_factors_comp_self _ _
      let b := (T.Z (r + 1) p q).factorThru (X.initialG p q) hfac
      have hb : b ≫ Subobject.ofLE _ _ (T.Z_decreasing r p q) = a := by
        apply (cancel_mono (T.Z r p q).arrow).mp
        simp [b, ha, Category.assoc]
      refine ⟨b, by simp [b], ?_⟩
      let Y := X.pageCouple r
      let M := Classical.choice Y.derivedMaps_exists
      have hmono : Mono (Y.derivedDInclusion (p + 2) (q - 1)) := by
        dsimp [BigradedExactCouple.derivedDInclusion]
        infer_instance
      let := hmono
      apply (cancel_mono (Y.derivedDInclusion (p + 2) (q - 1))).mp
      change (b ≫ T.projection (r + 1) p q ≫ M.f p q) ≫
        Y.derivedDInclusion (p + 2) (q - 1) = _
      rw [Category.assoc]
      rw [T.projection_succ, Category.assoc, Category.assoc, M.f_comm, zero_comp]
      change b ≫ T.cycleLift r p q ≫
        kernel.ι ((X.pageCouple r).d p q) ≫ (X.pageCouple r).f p q = _
      rw [← Category.assoc (T.cycleLift r p q), T.cycleLift_comm]
      simp only [← Category.assoc]
      rw [hb]
      simpa only [Category.assoc] using hf
  obtain ⟨a, ha, _⟩ := hfinite r
  exact (Subobject.factors_iff _ _).mpr ⟨a, ha⟩

private theorem quotient_homology_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n p' n' : ℤ) (hp : p = p') (hn : n = n') :
    HomologicalComplex.homologyMap (F.complexQuotientπ p (p + 1) (by omega)) n ≍
      HomologicalComplex.homologyMap (F.complexQuotientπ p' (p' + 1) (by omega)) n' := by
  subst p' n'
  rfl

set_option linter.unusedVariables false in
/-- The canonical derived-couple differential differentiates simultaneous filtered
representatives. The maps into the tower are fixed by their initial-homology
normalization; no quotient isomorphism is supplied or asserted here.
Source: Stacks Project, Tag 011R, derived-map restriction equations, and Tag 012K,
Lemma 12.24.2, differential on representatives.
(blueprint: lem-sp-filtered-homology-tower-differential).

Proof. The ambient differential squares to zero, and the filtration inclusion is
monic, so a' lifts uniquely to a cycle b in F^(p+s+1). Obtain the canonical
monic inclusions I of the derived D objects and the concrete iterated image
lift e of alphaIter. The forward-representative theorem identifies the page f
of x with the homology class of b followed by e. The finite-cycle formula
places initial g in the tower cycles, and the proved derived-g comparison
identifies e followed by page g with this factorization followed by the tower
projection. Naturality of homologyπ for the graded projection, together with
hy, hj and ht, identifies this factorization on b with y followed by tQ.
Compose the forward equation with g and transport the integer indices to
obtain the stated differential equation. The supplied hBZ, eH and hH are
unnecessary for this direct representative calculation. -/
theorem filteredHomology_tower_differential
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
    (tQ : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow)
    (ht : ∀ (s : ℕ) (p q : ℤ),
      tQ s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (s : ℕ) (p q : ℤ)
    (A : C)
    (a : A ⟶ (U.obj.filtration.step p : CochainComplex C ℤ).X (p + q))
    (a' : A ⟶ (U.obj.filtration.step (p + (s + 1)) :
      CochainComplex C ℤ).X (p + (s + 1) + (q - (s + 1) + 1)))
    (x : A ⟶ (U.obj.filtration.complexCycles p (p + q) (s + 1) : C))
    (y : A ⟶ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1) : C))
    (ha : a ≫ (U.obj.filtration.step p).arrow.f (p + q) ≫
      U.obj.obj.d (p + q) (p + (s + 1) + (q - (s + 1) + 1)) =
      a' ≫ (U.obj.filtration.step (p + (s + 1))).arrow.f
        (p + (s + 1) + (q - (s + 1) + 1)))
    (hx : x ≫ (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow =
      a ≫ (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (hy : y ≫ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1)).arrow =
      a' ≫ (U.obj.filtration.complexQuotientπ (p + (s + 1))
        (p + (s + 1) + 1) (by omega)).f
          (p + (s + 1) + (q - (s + 1) + 1))) :
    x ≫ tQ s p q ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * p + q) (-p) ≫
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).d
          (2 * p + q) (-p) ≫
        eqToHom (congrArg₂
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
          (show 2 * p + q + 2 + s =
            2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
          (show -p - 1 - s = -(p + (s + 1)) by omega)) =
      y ≫ tQ s (p + (s + 1)) (q - (s + 1) + 1) ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1))) := by
  clear hH eH hBZ
  let F := U.obj.filtration
  let X := filteredHomologyExactCouple U.obj.obj F
  let T := X.cycleBoundaryTower
  let p' := p + (s + 1)
  let q' := q - (s + 1) + 1
  let P := 2 * p' + q'
  let Q := -p'
  let n' := p' + q'
  have hda' : a' ≫ (F.step p' : CochainComplex C ℤ).d n' (n' + 1) = 0 := by
    apply (cancel_mono ((F.step p').arrow.f (n' + 1))).mp
    simp only [Category.assoc, zero_comp]
    rw [← (F.step p').arrow.comm]
    rw [← Category.assoc a', ← ha]
    simp only [n', p', q', Category.assoc, U.obj.obj.d_comp_d, comp_zero]
  let b : A ⟶ (F.step p' : CochainComplex C ℤ).cycles n' :=
    (F.step p' : CochainComplex C ℤ).liftCycles (i := n') a' (n' + 1) (by simp) hda'
  have hb : b ≫ (F.step p' : CochainComplex C ℤ).iCycles n' = a' := by
    simp only [b, HomologicalComplex.liftCycles_i]
  obtain ⟨_, I, _, _, hI0, hIs, hImono, _, _⟩ := X.pageCouple_image_prefix
  let e := BigradedExactCouple.comparisonLift X s P Q
  have he : e ≫ I s (P - s) (Q + s) = X.alphaIter s P Q :=
    BigradedExactCouple.comparisonLift_inclusion X I hI0 hIs s P Q
  have haB : a ≫ (F.step p).arrow.f (p + q) ≫ U.obj.obj.d (p + q) n' =
      b ≫ (F.step p' : CochainComplex C ℤ).iCycles n' ≫ (F.step p').arrow.f n' := by
    rw [← Category.assoc b, hb]
    exact ha
  have hf := filteredHomology_tower_forward_representatives C U j tQ hj ht
    I hI0 hIs hImono s p q e he A a b x haB hx
  let eD : (F.step p' : CochainComplex C ℤ).homology n' ≅ X.D P Q :=
    eqToIso (by
      change (F.step p' : CochainComplex C ℤ).homology n' =
        (F.step (-Q) : CochainComplex C ℤ).homology (P + Q)
      dsimp [P, Q, n']
      rw [neg_neg]
      congr 1; omega)
  let β := b ≫ (F.step p' : CochainComplex C ℤ).homologyπ n' ≫ eD.hom
  change x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
      (X.pageCouple s).f (2 * p + q) (-p) ≫ _ =
      b ≫ (F.step p' : CochainComplex C ℤ).homologyπ n' ≫ eD.hom ≫ e at hf
  have hg : (T.Z s P Q).Factors (X.initialG P Q) :=
    initialG_factors_tower_cycles X s P Q
  let c := (T.Z s P Q).factorThru (X.initialG P Q) hg
  have hG := X.finiteCycle_derived_comparison I hI0 hIs hImono s P Q hg e he
  have hgnorm : eD.hom ≫ X.initialG P Q ≫
      (filteredHomologyEIso U.obj.obj F p' q').hom =
      HomologicalComplex.homologyMap (F.complexQuotientπ p' (p' + 1) (by omega)) n' := by
    apply eq_of_heq
    simp only [eD, filteredHomologyEIso, eqToIso.hom, BigradedExactCouple.initialG,
      X, filteredHomologyExactCouple, filteredHomologyG, ← Category.assoc,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact quotient_homology_heq U.obj.obj F _ _ _ _
      (by dsimp [Q]; omega) (by dsimp [P, Q, n']; omega)
  have hcycles : b ≫ HomologicalComplex.cyclesMap
      (F.complexQuotientπ p' (p' + 1) (by omega)) n' = y ≫ j s p' q' := by
    dsimp only [F, n']
    apply (cancel_mono ((U.obj.filtration.gradedPiece p').iCycles (p' + q'))).mp
    erw [Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc b, hb, Category.assoc y, hj]
    exact hy.symm
  have hcy : β ≫ c = y ≫ tQ s p' q' := by
    apply (cancel_mono (T.Z s P Q).arrow).mp
    apply (cancel_mono (filteredHomologyEIso U.obj.obj F p' q').hom).mp
    simp only [β, c, Category.assoc, Subobject.factorThru_arrow]
    erw [hgnorm, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc b, hcycles]
    dsimp only [F, X, T, P, Q, n']
    erw [Category.assoc, ← ht s p' q']
  have hfg := congrArg
    (fun f ↦ f ≫ (X.pageCouple s).g (P - s) (Q + s) ≫
      eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
        (X.pageCouple s).E P Q by congr 1 <;> omega)) hf
  have hleft : x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
      (X.pageCouple s).d (2 * p + q) (-p) ≫
        eqToHom (show (X.pageCouple s).E (2 * p + q + 2 + s) (-p - 1 - s) =
          (X.pageCouple s).E P Q by congr 1 <;> dsimp [P, Q, p', q'] <;> omega) =
      x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
        (X.pageCouple s).f (2 * p + q) (-p) ≫
          eqToHom (show (X.pageCouple s).D (2 * p + q + 2) (-p - 1) =
            (X.pageCouple s).D (P - s) (Q + s) by
              congr 1 <;> dsimp [P, Q, p', q'] <;> omega) ≫
          (X.pageCouple s).g (P - s) (Q + s) ≫
          eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
            (X.pageCouple s).E P Q by congr 1 <;> omega) := by
    have hnat := eqToHom_naturality (fun pq : ℤ × ℤ ↦ (X.pageCouple s).g pq.1 pq.2)
      (show (2 * p + q + 2, -p - 1) = (P - s, Q + s) by
        ext <;> dsimp [P, Q, p', q'] <;> omega)
    have hnat' := congrArg (fun f ↦ f ≫
      eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
        (X.pageCouple s).E P Q by congr 1 <;> omega)) hnat
    simp only [Category.assoc, eqToHom_trans] at hnat'
    simpa only [BigradedExactCouple.d, Category.assoc] using congrArg
      (fun f ↦ x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
        (X.pageCouple s).f (2 * p + q) (-p) ≫ f) hnat'
  calc
    _ = _ := hleft
    _ = β ≫ e ≫ (X.pageCouple s).g (P - s) (Q + s) ≫
        eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
          (X.pageCouple s).E P Q by congr 1 <;> omega) := by
      simpa only [β, Category.assoc] using hfg
    _ = β ≫ c ≫ T.projection s P Q := by
      simpa only [c, Category.assoc] using congrArg (fun f ↦ β ≫ f) hG
    _ = _ := by
      rw [← Category.assoc, hcy]
      dsimp only [F, X, T, P, Q, p', q']
      simp only [Category.assoc]

end CategoryTheory
```

The following two replacement helper proofs were also checked in the same explicit
scratch construction. They belong to the separately held forward-representative
module and are recorded here only as recovery material; that module is not
changed by this delivery. Its other helpers and its commented public forward
proof already provide the remaining calculation. These proofs require the
canonical concrete definitions, and they use its existing private
`inclusion_homology_heq` helper.

```lean
private theorem filtered_alphaIter
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (s : ℕ) (P Q : ℤ) :
    (filteredHomologyExactCouple K F).alphaIter s P Q ≍
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + (s : ℤ))))
          (F.antitone_step (by omega))) (P + Q) := by
  induction s generalizing P Q with
  | zero =>
    dsimp only [BigradedExactCouple.alphaIter]
    apply (eqToHom_heq_id_dom ((filteredHomologyExactCouple K F).D P Q) _ _).trans
    symm
    have h := inclusion_homology_heq K F (-Q) (-(Q + ((0 : ℕ) : ℤ))) (-Q) (-Q)
      (P + Q) (P + Q) (by omega) le_rfl rfl (by omega) rfl
    apply h.trans
    apply heq_of_eq
    simp only [Subobject.ofLE_refl, HomologicalComplex.homologyMap_id]
  | succ s ih =>
    simp only [BigradedExactCouple.alphaIter, ← Category.assoc,
      comp_eqToHom_heq_iff]
    let a := Subobject.ofLE (F.step (-Q)) (F.step (-(Q + 1)))
      (F.antitone_step (show -(Q + 1) ≤ -Q by omega))
    let b := Subobject.ofLE (F.step (-(Q + 1))) (F.step (-(Q + (s + 1 : ℕ))))
      (F.antitone_step (by omega))
    have hit : (filteredHomologyExactCouple K F).alphaIter s (P - 1) (Q + 1) ≍
        HomologicalComplex.homologyMap b (P + Q) := by
      apply (ih (P - 1) (Q + 1)).trans
      exact inclusion_homology_heq K F _ _ _ _ _ _ (by omega) (by omega)
        rfl (by omega) (by omega)
    have hcomp :
        (filteredHomologyExactCouple K F).alpha P Q ≫
          (filteredHomologyExactCouple K F).alphaIter s (P - 1) (Q + 1) ≍
        HomologicalComplex.homologyMap a (P + Q) ≫
          HomologicalComplex.homologyMap b (P + Q) := by
      change (HomologicalComplex.homologyMap a (P + Q) ≫ eqToHom _) ≫ _ ≍ _
      simp only [Category.assoc]
      refine heq_comp rfl rfl ?_ HEq.rfl ((eqToHom_comp_heq _ _).trans hit)
      change (F.step (-((Q + 1) + (s : ℤ))) : CochainComplex C ℤ).homology
          ((P - 1 - (s : ℤ)) + (Q + 1 + s)) = _
      apply congrArg₂ (fun z n ↦ (F.step z : CochainComplex C ℤ).homology n) <;> omega
    apply hcomp.trans
    apply heq_of_eq
    rw [← HomologicalComplex.homologyMap_comp]
    simp only [a, b, Subobject.ofLE_comp_ofLE]


private theorem filtered_initial_f
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ) :
    (filteredHomologyEIso K F p q).inv ≫
        (filteredHomologyExactCouple K F).f (2 * p + q) (-p) ≍
      (filteredStep_shortExact K F p).δ (p + q) (p + q + 1) rfl := by
  simp only [filteredHomologyEIso, eqToIso.inv, filteredHomologyExactCouple, filteredHomologyF,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact connecting_heq K F _ _ _ _ (by omega) (by omega)

```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
