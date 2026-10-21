/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.TraceFormula.SemistableMarkedPoint
public import Sheaf.TraceFormula.LocalMarkingLength
public import Sheaf.TraceFormula.ProjectiveLineTree
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.TraceFormula.GenusZeroSmoothProperLine
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
import Sheaf.TraceFormula.MultipointedCurve
import Sheaf.TraceFormula.NodalContractionNormalizationBranches
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches

/-! # The exceptional-tree criterion for a marked curve contraction

Source: Temkin, *Stable modification of relative curves*, Lemma 4.4.2, pp. 30–31,
and Appendix B, Corollary B.2, pp. 57–58
(blueprint: lem-trf-curve-p1-tree-local-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper contraction of marked reduced curves of equal arithmetic genus has a
semistable marked image point exactly when its scheme-theoretic fibre is an exceptional
projective-line tree. The closed point `x` is equivalently a `k`-point, by
`pointEquivClosedPoint`. Its residue field is canonically `k`, so the recorded fibre
`f.fiber x` is precisely the scheme-theoretic fibre over that rational point.

Source: Temkin, Lemma 4.4.2 and Appendix B, Corollary B.2, pp. 30–31 and 57–58
(blueprint: lem-trf-curve-p1-tree-local-criterion).

Proof, following the eight steps of the DAG node:
1. Put `B = Z_red`. It has the same support, boundary and marking counts as `Z`.
   The reduced-induced-subscheme and nodal-subcurve-boundary lemmas make `B` nodal,
   with smooth boundary. The normalization-genus lemma supplies its component genera.
2. Apply nodal-contraction-normalization-branches: the noncontracted normalizations
   agree, and the branches of the target at `x` correspond to the boundary, of size `n ≥ 1`.
3. Subtract the normalization-genus formulas. With `v` components, `e` internal nodes
   and component genera `g_i`, equality of arithmetic genera gives
   `delta_C(x) = n - 1 + (e - v + 1) + sum_i g_i`. Ordinary-point-delta-branches
   supplies delta one at each node and zero at each smooth point.
4. Connectedness gives a connected incidence multigraph. A spanning tree has `v - 1`
   edges; hence `e - v + 1 ≥ 0`, with equality precisely for a tree. All `g_i ≥ 0`.
5. A tree has no self-nodes, so its components are smooth and normal by the
   nodal-subcurve-boundary and smooth-normal lemmas. Genus-zero-smooth-proper-line
   identifies genus-zero components with the projective line; projective-line-genus-zero
   gives the converse.
6. Ordinary-point-delta-branches identifies `delta_C(x) = n - 1` with an ordinary
   `n`-fold target point. In these cases the reduced-fibre clause of
   nodal-contraction-normalization-branches gives `Z = B`, retaining the actual fibre.
7. Write `m` for the number of source markings on `Z`. Conservation of local marking
   length makes the target marking absent for `m = 0` and a reduced `k`-point for `m = 1`.
   Conversely an etale local finite marking has length one, by the
   etale-algebra-over-field-product lemma and algebraic closure. At a smooth target
   point precisely `m = 0, 1` are allowed; a nodal target requires `m = 0`.
8. Since `n ≥ 1`, the possibilities for `n + m ≤ 2` are `(1,0)`, `(1,1)` and `(2,0)`.
   These are exactly the semistable marked target cases. This proves both directions.
-/
theorem curve_p1_tree_local_criterion
    {k : Type u} [Field k] [IsAlgClosed k]
    (P' P : MultipointedCurve (Spec (.of k)))
    [IsProper P'.x] [IsProper P.x] [IsReduced P'.X] [IsReduced P.X]
    [IsFinite P'.d] [IsFinite P.d]
    (f : P'.X ⟶ P.X) (fD : P'.D ⟶ P.D)
    (hf : f ≫ P.x = P'.x) (hfD : fD ≫ P.d = P'.d)
    (hmark : fD ≫ P.i = P'.i ≫ f) [IsProper f] [Surjective f]
    (hgenus :
      1 - @Scheme.Modules.eulerChar k _ P'.X ⟨P'.x⟩
        (SheafOfModules.unit P'.X.ringCatSheaf) =
      1 - @Scheme.Modules.eulerChar k _ P.X ⟨P.x⟩
        (SheafOfModules.unit P.X.ringCatSheaf))
    (x : P.X) (hx : IsClosed ({x} : Set P.X))
    [ConnectedSpace (f.fiber x)]
    (hpure : (f.fiber x).IsPureDimension 1)
    (hoff : IsIso (pullback.snd f
      (Scheme.Opens.ι (X := P.X) ⟨{x}ᶜ, hx.isOpen_compl⟩)))
    (hsemi : ∀ z : f.fiber x,
      (MultipointedPair.ofCurve P').IsSemistableAt (f.fiberι x z))
    (hlength : (P.localMarkingLength x : ℕ∞) =
      (Set.range P'.i ∩ Set.range (f.fiberι x)).encard) :
    (MultipointedPair.ofCurve P).IsSemistableAt x ↔
      IsProjectiveLineTree (f.fiberι x ≫ P'.x) ∧
      (Set.range (f.fiberι x) ∩ closure (Set.range (f.fiberι x))ᶜ).encard +
        (Set.range P'.i ∩ Set.range (f.fiberι x)).encard ≤ 2 := by
  sorry

end AlgebraicGeometry
