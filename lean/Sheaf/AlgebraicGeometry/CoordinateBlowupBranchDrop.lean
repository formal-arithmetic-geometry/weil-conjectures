/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount
public import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Compactification.StrictTransform
import Sheaf.RingTheory.Etale.LocalDimension
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Affine.Principalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Blowup.BaseChange
import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
import Sheaf.RingTheory.IsRegularSystemOfParameters
import Sheaf.TraceFormula.CoordinateMaximalBranchStratum
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Coordinate blowups lower the branch number

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, Lemma 4.2.9,
printed p. 121, and 4.1.8, printed p. 118
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop).

The auxiliary definitions name the canonical chart rings, their actual fraction coordinates,
and the clauses of the chart calculation, including arbitrary etale base changes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.CoordinateBlowupBranchDrop

variable {R : Type u} [CommRing R] {m : ℕ}

/-- The centre ideal sheaf for the entire coordinate list, using the published construction.
Source: ILO VIII 4.2.9 (blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
abbrev centerSheaf (t : Fin m → R) : (Spec (.of R)).IdealSheafData :=
  PermissibleCoordinateChart.centerSheaf t Finset.univ

/-- The actual subalgebra `R[I/t_i]` of `R[1/t_i]`.
Source: ILO VIII 4.2.9 (blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
abbrev chartRing (t : Fin m → R) (i : Fin m) : Type u :=
  AffineBlowup.chartRing (PermissibleCoordinateChart.center t Finset.univ) (t i)

/-- The fraction `t_j/t_i`, as an element of the canonical chart subalgebra.
Source: ILO VIII 4.2.9 (blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def ratio (t : Fin m → R) (i j : Fin m) : chartRing t i :=
  ⟨AffineBlowup.chartFraction (t i) 1 (t j),
    Algebra.subset_adjoin ⟨⟨t j, Ideal.subset_span
      ⟨j, Finset.mem_univ j, rfl⟩⟩, rfl⟩⟩

/-- The product of precisely the nonexceptional ratio coordinates; it is `1` for `m=1`.
Source: ILO VIII 4.1.8, 4.2.9
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def strictEquation (t : Fin m → R) (i : Fin m) : chartRing t i :=
  ∏ j ∈ Finset.univ.erase i, ratio t i j

/-- The chart structure map induced by the canonical algebra map.
Source: ILO VIII 4.2.9 (blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def projection (t : Fin m → R) (i : Fin m) :
    Spec (.of (chartRing t i)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (chartRing t i)))

/-- The principal closed subscheme, represented by its quasi-coherent ideal sheaf.
Source: ILO VIII 4.1.8, 4.2.9
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def divisor (a : R) : (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {a}).map (Scheme.ΓSpecIso (.of R)).inv.hom)

/-- The pointwise coordinate hypothesis: exactly the functions in a prime occur in distinct
positions in a regular parameter system of the local ring at that prime.
Source: ILO VIII 4.2.9, with localization at each chosen point
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def HasCoordinateParameters [IsNoetherianRing R] (t : Fin m → R) : Prop :=
  ∀ p : PrimeSpectrum R,
    ∃ s : List (Localization.AtPrime p.asIdeal),
      IsLocalRing.IsRegularSystemOfParameters s ∧
      ∃ f : {j : Fin m // t j ∈ p.asIdeal} → Fin s.length,
        Function.Injective f ∧
        ∀ j, s.get (f j) = algebraMap R (Localization.AtPrime p.asIdeal) (t j)

/-- The exact germ of a chart coordinate after any scheme morphism into the chart.
Source: ILO VIII 4.2.9 and its etale pullbacks
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def coordinateGerm (t : Fin m → R) (i : Fin m)
    {W : Scheme.{u}} (h : W ⟶ Spec (.of (chartRing t i))) (y : W) (j : Fin m) :
    W.presheaf.stalk y :=
  (h.stalkMap y).hom
    ((StructureSheaf.toStalk (chartRing t i) (h y)).hom (ratio t i j))

/-- The exact germ of the strict-transform product after a morphism into the chart.
Source: ILO VIII 4.1.8, 4.2.9
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def equationGerm (t : Fin m → R) (i : Fin m)
    {W : Scheme.{u}} (h : W ⟶ Spec (.of (chartRing t i))) (y : W) :
    W.presheaf.stalk y :=
  (h.stalkMap y).hom
    ((StructureSheaf.toStalk (chartRing t i) (h y)).hom (strictEquation t i))

open Classical in
/-- The pointwise conclusions on a chart or its etale pullback: regularity, the exact vanishing
coordinate germs in distinct parameter positions, unit factors, the local product expression,
normal crossings, the geometric branch equality and bound, and the empty `m=1` case.
Source: ILO VIII 4.1.8, 4.2.9
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def LocalChartProperties (t : Fin m → R) (i : Fin m)
    {W : Scheme.{u}} (h : W ⟶ Spec (.of (chartRing t i))) : Prop :=
  IsRegularScheme W ∧
  (∀ y : W,
    ∃ (hN : IsNoetherianRing (W.presheaf.stalk y)) (s : List (W.presheaf.stalk y)),
      @IsLocalRing.IsRegularSystemOfParameters (W.presheaf.stalk y) _ _ hN s ∧
      (∃ f : {j : Fin m // j ≠ i ∧
          coordinateGerm t i h y j ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y)} →
            Fin s.length,
        Function.Injective f ∧ ∀ j, s.get (f j) = coordinateGerm t i h y j) ∧
      (∀ j : Fin m, j ≠ i →
        coordinateGerm t i h y j ∉ IsLocalRing.maximalIdeal (W.presheaf.stalk y) →
          IsUnit (coordinateGerm t i h y j)) ∧
      (∃ (v : (W.presheaf.stalk y)ˣ) (J : Finset (Fin s.length)),
        equationGerm t i h y = (v : W.presheaf.stalk y) * ∏ k ∈ J, s.get k)) ∧
  ((divisor (strictEquation t i)).comap h).IsNormalCrossingsDivisor ∧
  (∀ y : W,
    ((divisor (strictEquation t i)).comap h).ncBranchCount y =
      (Finset.univ.filter (fun j : Fin m ↦ j ≠ i ∧
        coordinateGerm t i h y j ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y))).card ∧
    ((divisor (strictEquation t i)).comap h).ncBranchCount y ≤ m - 1) ∧
  (m = 1 → strictEquation t i = 1 ∧
    IsEmpty ((divisor (strictEquation t i)).comap h).subscheme)

/-- The chart equations on an arbitrary base change, with actual scheme-theoretic strict
transforms. The chart sources are the canonical fibre products. Their embeddings into the
base-changed-centre blowup commute with the structure maps and cover it.
Source: ILO VIII 4.1.8, 4.2.9; Stacks Tags 0805, 080D
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop). -/
def BaseChangedChartProperties (t : Fin m → R)
    {S : Scheme.{u}} (q : S ⟶ Spec (.of R)) : Prop :=
  (∃ c : ∀ i : Fin m,
      pullback q (projection t i) ⟶ ((centerSheaf t).comap q).blowup,
    (∀ i, IsOpenImmersion (c i) ∧
      c i ≫ ((centerSheaf t).comap q).blowupMap = pullback.fst q (projection t i)) ∧
    (∀ y : ((centerSheaf t).comap q).blowup,
      ∃ (i : Fin m) (z : ↥(pullback q (projection t i))), c i z = y)) ∧
  (∀ i : Fin m,
    (strictTransformMap ((divisor (∏ j : Fin m, t j)).comap q).subschemeι
      (pullback.fst q (projection t i))
      ((centerSheaf t).comap q).support.compl).ker =
        (divisor (strictEquation t i)).comap (pullback.snd q (projection t i)) ∧
    LocalChartProperties t i (pullback.snd q (projection t i)))

/-- The coordinate blowup calculation over a general regular Noetherian affine ring.
All parameter assertions concern the local ring at each chosen point; neither the base
ring nor a chart ring is assumed local. The last clause gives the same equations and
pointwise assertions after every etale base change, with canonical fibre-product charts.

Source: ILO VIII, Lemma 4.2.9, printed p. 121, and 4.1.8, printed p. 118
(blueprint: lem-trf-nc-coordinate-blowup-branch-drop).

Proof:
1. The standard blowup chart cover has rings `R[I/t_i]`. The chart algebra construction
and principalization give `t_j=t_i z_j`, `I R[I/t_i]=(t_i)` and `f=t_i^m P`.
2. Fix a chart prime and localize at its image in `R`. Off the centre a generator is a
unit, hence `t_i` is a unit and the chart local ring is the original local ring. Ratios
are unit multiples of the original coordinate parameters.
3. Over the centre, complete the coordinate germs to parameters and apply
`lem-trf-permissible-coordinate-chart`. Its pointwise parameter assertion gives regularity
and distinct parameter positions for all vanishing ratios and the exceptional equation.
4. Strict transforms are scheme-theoretic closures off the centre. The quasi-compact
preserved open and the scheme-image restriction theorem identify the chart ideal with
`ker(C -> (C/(f))[1/t_i])`, or the saturation of `(f)` by `t_i`.
5. In every chart local ring, unique factorization of regular parameters shows that
saturating `(t_i^m P)` by `t_i` gives exactly `(P)`: the nonunit factors of `P` are distinct
prime parameters not associated to `t_i`. Equality of stalks proves the ideal equality.
The empty product when `m=1` is `1`, giving the empty strict transform.
6. The product is a nonzerodivisor in each regular local ring, hence defines an effective
Cartier divisor. The coordinate parameter presentations give normal crossings.
`lem-trf-nc-coordinate-max-stratum` identifies its geometric branches with precisely the
vanishing ratio factors, whose number is at most `m-1` (zero for the empty product).
7. Blowups commute with flat etale base change (Stacks 0805). Flat tensor exactness
preserves the closure kernel; quotient and localization commute with tensor, so the
pulled-back strict transform has exactly the pulled-back product equation.
8. The chart projection after base change is etale. Its local maps preserve units, extend
the maximal ideals, and preserve local dimension (Stacks 00U4, 07QP). Parameter systems
therefore remain parameter systems at every chosen point. This proves all the local
clauses and branch counts on the base-changed charts, which cover the new blowup.
-/
theorem coordinate_blowup_branch_drop
    {R : Type u} [CommRing R] [IsRegularRing R]
    (m : ℕ) (t : Fin m → R) (hm : 1 ≤ m) (ht : HasCoordinateParameters t) :
    (∀ i : Fin m,
      AffineBlowup.chartRing (PermissibleCoordinateChart.center t Finset.univ) (t i) =
        Algebra.adjoin R (Set.range (fun j : {j : Fin m // j ≠ i} ↦
          AffineBlowup.chartFraction (t i) 1 (t j))) ∧
      (∀ j : Fin m, algebraMap R (chartRing t i) (t j) =
        algebraMap R (chartRing t i) (t i) * ratio t i j) ∧
      (strictTransformMap (divisor (∏ j : Fin m, t j)).subschemeι
        (projection t i) (centerSheaf t).support.compl).ker =
          divisor (strictEquation t i) ∧
      IsRegularRing (chartRing t i) ∧
      LocalChartProperties t i (𝟙 (Spec (.of (chartRing t i))))) ∧
    (∀ (S : Scheme.{u}) (q : S ⟶ Spec (.of R)), Etale q →
      BaseChangedChartProperties t q) := by
  sorry

end AlgebraicGeometry.CoordinateBlowupBranchDrop
