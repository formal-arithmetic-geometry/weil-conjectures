/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.TraceFormula.Modification
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.TraceFormula.AbhyankarFiniteTypeFieldHeight
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous
import Sheaf.AlgebraicGeometry.NagataMorphismDescends
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.BirationalQuasiModificationCommonCover
import Sheaf.TraceFormula.BaseModificationComparisonFibreImage
import Sheaf.AlgebraicGeometry.BirationalRiemannZariskiNeighbourhoods

/-! # Valuative domination for eta-normal schemes

Source: Temkin, *Stable modification of relative curves*, Proposition 5.2,
printed pp. 34--35 (blueprint: lem-trf-valuative-domination-eta-normal).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Valuative domination by an eta-normal flat reduced scheme.

Source: Temkin, *Stable modification of relative curves*, Proposition 5.2,
printed pp. 34--35, and the finite-height reduction in the proof of Theorem 1.2
(blueprint: lem-trf-valuative-domination-eta-normal).

Proof:
1. Finite type over the Noetherian base gives Noetherianness and finite presentation
   (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-finite-type-noetherian-finite-presentation`). The function field of
   a finite-type integral Z-scheme has finite-height valuations by
   `lem-trf-abhyankar-finite-type-field-height`.
2. Flatness and torsion-free sections (`lem-sc-flat-invertible-sections-torsion-free`,
   the affine flatness criterion) give schematic generic density after integral
   birational base change. A separated equalizer then gives generic uniqueness.
3. `lem-trf-birational-riemann-zariski-neighbourhoods` and
   `lemma-nagata-morphism-descends` spread each valuative comparison to a birational
   affine neighbourhood. Quasi-compactness gives finitely many such neighbourhoods.
4. `lem-trf-birational-quasi-modification-common-cover` provides an integral proper
   modification of S on whose open cover the comparisons glue by generic uniqueness.
   Removing the proper image of the complement of its isomorphism open gives a dense
   base open over which this modification is an isomorphism.
5. Close the generic graph in Y ×_C X. Proper permanence makes its projection to Y
   proper. Spread the generic map by `lemma-nagata-morphism-descends`; over a dense
   base open the closure is its graph. Generic density gives schematic density on
   both sides and reducedness of the graph closure.
6. The comparison after base modification factors through this closure by generic
   density. Its graph and proper permanence make the factor proper, and its image
   contains the dense generic graph, so it surjects onto the closure.
7. At a closed point y of Y, `lem-trf-base-modification-comparison-fibre-image`
   gives a finite set of image points in X_s. The closed-point field lemma
   `lem-kun-closed-point-field` makes κ(y)/κ(s) finite. Thus the graph fibre is a
   closed subscheme of finitely many finite spectra κ(y) ⊗_κ(s) κ(x), so has
   dimension at most zero.
8. Proper fibre-dimension upper semicontinuity extends this bound from closed
   points to all Y. The relative-dimension-zero criterion makes the projection
   locally quasi-finite; `pqf-lem-proper-lqf-finite` makes it finite. It is a finite
   eta-modification, hence an isomorphism by the assumed eta-normality.
9. The inverse graph projection followed by the other projection is the required
   S-map; the fibre-product equation gives h ≫ a = b, and its generic fibre is
   b_eta followed by the inverse of a_eta.
-/
theorem valuative_domination_eta_normal
    {S : Scheme.{u}} [IsIntegral S]
    (s : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType s] [QuasiCompact s]
    {C X Y : Scheme.{u}} (c : C ⟶ S)
    (a : X ⟶ C) (b : Y ⟶ C)
    [IsReduced C] [IsReduced X] [IsReduced Y]
    [Flat c] [Flat (a ≫ c)] [Flat (b ≫ c)]
    [LocallyOfFiniteType c] [QuasiCompact c]
    [LocallyOfFiniteType (a ≫ c)] [QuasiCompact (a ≫ c)]
    [LocallyOfFiniteType (b ≫ c)] [QuasiCompact (b ≫ c)]
    (ha : EtaModification (S.fromSpecStalk (genericPoint S)) a c)
    (hb : EtaModification (S.fromSpecStalk (genericPoint S)) b c)
    (hnormal : ∀ {Z : Scheme.{u}} (f : Z ⟶ Y),
      IsFinite f → EtaModification (S.fromSpecStalk (genericPoint S)) f (b ≫ c) →
        IsIso f)
    (hvaluative : ∀ (V : ValuationSubring S.functionField), Finite (PrimeSpectrum V) →
      ∀ (v : Spec (CommRingCat.of V) ⟶ S),
        Spec.map (CommRingCat.ofHom V.toSubring.subtype) ≫ v =
          S.fromSpecStalk (genericPoint S) →
        ∃ hV : (Over.pullback v).obj (Over.mk (b ≫ c)) ⟶
            (Over.pullback v).obj (Over.mk (a ≫ c)),
          hV ≫ (Over.pullback v).map
              (Over.homMk a rfl : Over.mk (a ≫ c) ⟶ Over.mk c) =
            (Over.pullback v).map
              (Over.homMk b rfl : Over.mk (b ≫ c) ⟶ Over.mk c)) :
    ∃ h : Over.mk (b ≫ c) ⟶ Over.mk (a ≫ c),
      h.left ≫ a = b ∧
        ((Over.pullback (S.fromSpecStalk (genericPoint S))).map h).left =
          ((Over.pullback (S.fromSpecStalk (genericPoint S))).map
            (Over.homMk b rfl : Over.mk (b ≫ c) ⟶ Over.mk c)).left ≫
          @inv Scheme _ _ _
            (((Over.pullback (S.fromSpecStalk (genericPoint S))).map
              (Over.homMk a rfl : Over.mk (a ≫ c) ⟶ Over.mk c)).left) ha.2 := by
  sorry

end AlgebraicGeometry
