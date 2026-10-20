/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.CoordinateBlowupBranchDrop
import Sheaf.TraceFormula.CoordinateMaximalBranchStratum

/-!
# Blowing up the maximal geometric branch locus

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, 4.1.6 and 4.1.8,
printed p. 118; the local computation of 4.2.8--4.2.9, printed pp. 120--121
(blueprint: lem-trf-nc-maximal-branch-blowup).

## Main definitions and statements

* `ncStrictTransformIdeal` uses the canonical scheme-theoretic strict transform.
* `nc_maximal_branch_blowup` states the maximal-stratum construction and branch drop.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The defining ideal of the canonical scheme-theoretic strict transform of `D` on the
blowup of `I`. This is the kernel of the published strict-transform closed immersion,
so retains its scheme structure, rather than merely its underlying closed set.
Source: ILO VIII 4.1.8; Stacks Tag 080C
(blueprint: lem-trf-nc-maximal-branch-blowup). -/
def ncStrictTransformIdeal {X : Scheme.{u}} (I D : X.IdealSheafData) :
    I.blowup.IdealSheafData :=
  (AlgebraicGeometry.strictTransformMap D.subschemeι I.blowupMap I.support.compl).ker

/-- The maximal branch locus is a nonempty regular reduced closed center, has simultaneous
coordinate equations with the old boundary, and its blowup lowers the strict-transform
branch count everywhere.

Source: ILO VIII 4.1.6 and 4.1.8, printed p. 118, and 4.2.8--4.2.9, pp. 120--121
(blueprint: lem-trf-nc-maximal-branch-blowup).

Proof:
1. Use `lem-trf-nc-coordinate-max-stratum` in pointed affine etale normal crossings
charts, selecting the factors belonging to D and discarding unit factors. It identifies
branch counts independently of coordinates and describes every locus b_D >= k by finite
unions of coordinate intersections. Etale maps are open (`lem-weil-pbc-flat-lfp-open`).
Quasi-compactness gives a finite chart-image cover and hence a uniform finite bound.
Nonempty D supplies a positive attained value. Openness descends the complements of
these closed loci, so the maximal attained stratum is closed and nonempty.
2. Give it the reduced induced structure (`lem-weil-pbc-reduced-induced-closed-subscheme`).
The local maximal-stratum lemma identifies its pullback with the reduced regular coordinate
intersection. `lem-trf-etale-reduced-cartier-descent` identifies the reduced structures.
Etale base change and `lem-weil-pbc-flat-under-regular` descend regularity of its local
rings. Shrink the pointed charts to spread the simultaneous equations for B, D and M.
3. Blowup commutes with the flat etale charts (`thm-nagata-blowup-flat-base-change`).
Identify strict transforms by `lemma-nagata-strict-transform-closure-characterization`:
the preserved open is quasi-compact and quasi-separated, and is schematically dense in
its closure. `lemma-nagata-dense-flat-pullback` preserves that density under the etale
pullback; closed immersion base change makes its pullback the same closure.
4. Apply `lem-trf-nc-coordinate-blowup-branch-drop`. On the i-th chart the strict transform
has equation the product of t'_j for j != i. At any chart point its vanishing factors are
part of a regular system of parameters, and there are at most m - 1. For m = 1 the product
is 1 and the strict transform is empty. Etale base change supplies all points over M.
5. Away from M, `thm-nagata-global-blowup-complement` and
`lemma-nagata-strict-transform-over-complement` identify the strict transform with D.
The count there is less than m. This proves normal crossings and the bound everywhere.
-/
theorem nc_maximal_branch_blowup
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U))
    (B D : X.IdealSheafData) (hB : B.IsNormalCrossingsDivisor)
    (hDred : IsReduced D.subscheme) (hDne : Nonempty D.subscheme)
    (hcomponents : ∃ C : Set (Set B.subscheme),
      C ⊆ irreducibleComponents B.subscheme ∧
        (D.support : Set X) = ⋃ Z ∈ C, B.subschemeι '' Z) :
    ∃ (m : ℕ) (T : Closeds X), 1 ≤ m ∧
      (∀ x : X, D.ncBranchCount x ≤ m) ∧
      (T : Set X) = {x : X | D.ncBranchCount x = m} ∧
      (T : Set X).Nonempty ∧
      (∀ z : (vanishingIdeal T).subscheme,
        ∃ U : (vanishingIdeal T).subscheme.affineOpens,
          z ∈ U.1 ∧ IsRegularRing Γ((vanishingIdeal T).subscheme, U)) ∧
      (∀ x : X, x ∈ T →
        ∃ (W : Scheme.{u}) (e : W ⟶ X) (w : W),
          IsAffine W ∧ Etale e ∧ e w = x ∧
          ∃ (d r : ℕ) (hmr : m ≤ r) (hrd : r ≤ d)
            (t : Fin d → Γ(W, ⊤)) (hR : IsNoetherianRing (W.presheaf.stalk w)),
            @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk w) _ _ hR
              (List.ofFn (fun j : Fin d ↦ W.presheaf.germ ⊤ w (by trivial) (t j))) ∧
            D.comap e = ofIdealTop
              (Ideal.span {∏ j : Fin m, t (Fin.castLE (hmr.trans hrd) j)}) ∧
            B.comap e = ofIdealTop
              (Ideal.span {∏ j : Fin r, t (Fin.castLE hrd j)}) ∧
            (vanishingIdeal T).comap e = ofIdealTop
              (Ideal.span (Set.range (fun j : Fin m ↦ t (Fin.castLE (hmr.trans hrd) j))))) ∧
      (IsEmpty ((vanishingIdeal T).ncStrictTransformIdeal D).subscheme ∨
        ((vanishingIdeal T).ncStrictTransformIdeal D).IsNormalCrossingsDivisor) ∧
      (∀ y : (vanishingIdeal T).blowup,
        ((vanishingIdeal T).ncStrictTransformIdeal D).ncBranchCount y ≤ m - 1) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
