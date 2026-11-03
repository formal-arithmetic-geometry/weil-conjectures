/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.SpTowerChartCounit.SmoothPurityTowerChartCounit

/-! # The actual local chart adjunction with its specified counit

Source: latest blueprint, smooth tower gluing, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The specified local chart counit is an adjunction counit on the full ctf categories.
Source: latest blueprint `sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and
Uniformity (blueprint: lem-sp-tower-specified-local-chart-pair).

Proof. The uniform bound theorem and exact open extension and restriction preserve the
full constructible finite-Tor categories on U and X. In system coordinates restrict the
projective-line adjunction of each given presentation to those categories, using its
constructible_restriction field and chart admissibility. Compose with extension from
A1 to P1; its counit is direct image of the open counit followed by projectiveCounit.
Iterate these adjunctions in the specified coordinate order. Their counit is precisely
orderedCounit, by the formula for the counit of composite adjunctions. Compose with the
etale sum adjunction; its counit is the actual fibre sum. The compact-support splitting
and inverse graph comparison identify the left functor with F_c; their invertibility on
the chart objects follows from admissibility, etale comparison and the canonical
compact-support compositors. Transport the right functor along beta and both sides
through the section-preserving realizations. The formula for transport of an adjunction
counit is exactly chartCounit. The canonical twist has the local level bounds shifted
by -2d, so this transported adjunction restricts to the asserted full categories.
At d=0 the ordered adjunction is the identity. Empty opens use the same exact adjunctions.
This is a local adjunction and gives no global object, functor or gluing assertion. -/
theorem tower_specified_local_chart_pair
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (g : GraphCoordinates l E b o)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (t : ∀ r : ℕ, SpCoordinateAdjunction.ProjectivePresentation l E b o
      (affineTraceTower Y.left r))
    (U : X.left.Opens)
    (hU : IsSeparated (U.ι ≫ X.hom) ∧ LocallyOfFiniteType (U.ι ≫ X.hom) ∧
      QuasiCompact (U.ι ≫ X.hom))
    (e : U.toScheme ⟶ affineTraceTower Y.left d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : U.ι ≫ f.left = e ≫ affineTraceProjection Y.left d)
    (hOver : e ≫ affineTraceProjection Y.left d ≫ Y.hom = U.ι ≫ X.hom)
    (β : SpTowerChartCounit.chartRight l E b o e (affineTraceProjection Y.left d) d ≅
      SpTowerChartCounit.orderedRight l E b o Y.left t d ⋙
        SpTowerShriek.pull l E b (o.geometry e)) :
    (∀ M : SpTowerCalculus.C l E b q U.toScheme,
      spConstructibleTorTowers l E X.left (q.abelian X.left)
        ((SpTowerCalculus.openExtension l E b o q U.ι).obj M.obj)) ∧
    (∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E U.toScheme (q.abelian U.toScheme)
        ((SpTowerCalculus.etalePullback l E b o q U.ι).obj M.obj)) ∧
    ∃ pair : SpCoordinateAdjunction.RestrictedPair
      (spConstructibleTorTowers l E U.toScheme (q.abelian U.toScheme))
      (spConstructibleTorTowers l E Y.left (q.abelian Y.left))
      (SpTowerCalculus.F l E b o q
        (((CondensedRing.compactificationOverField f).precomp U.ι).copy he.symm))
      (SpTowerChartCounit.originalChartRight l E b o q e (affineTraceProjection Y.left d) d),
      ∀ K : SpTowerCalculus.C l E b q Y.left,
        pair.counit K =
          SpTowerChartCounit.chartCounit l E pchar hne k b o x laws q g
            ⟨Y, ⟨inferInstance, inferInstance, inferInstance⟩⟩ (openBase X U hU) d t e
            hOver (((CondensedRing.compactificationOverField f).precomp U.ι).copy he.symm)
            β K := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
