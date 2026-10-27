/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.AlgebraicGeometry.LCICurveFundamentalClass
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison

import Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization
import WeilConjectures.Topology.GlueSheavesOfModules
import Sheaf.RingTheory.RelativeRegularEquationsBaseChange

/-! # Gluing normalized adjunction and fundamental classes over locally Noetherian bases

Source: Stacks Project, duality.tex, Tags 0B6V, 0E2Y, 0E9Y, 0E9Z and 0BQZ;
sheaves.tex, Tags 04TN, 00AL, 00AM and 00AN. This is affine-refinement assembly
of the recorded adjunction and fundamental-class statements, including their
specified determinant and signed Koszul comparisons.
(blueprint: lem-sfb-locnoeth-lci-curve-adjunction-gluing).

The identity member of the system is the global pair on X. Other members include
all affine base opens, all their refinements, arbitrary changes to non-Noetherian
bases, and isomorphic families. The same system's identity and composition fields
are the restriction identity and triple-overlap cocycle equalities. No affine
intersection, properness, separatedness, or nodality assumption is made.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Forget only regularity and the rank equation of an existing polynomial lci chart.
The open, ambient scheme, immersion and polynomial coordinates are unchanged.
Source: Stacks, Tags 0B6V and 0BQZ
(blueprint: lem-sfb-locnoeth-lci-curve-adjunction-gluing). -/
def FlatLCIPresentation.polynomialChart {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C : FlatLCIPresentation p d U) : RelativeDualityPolynomialChart p where
  U := U
  n := C.n
  P := C.P
  ambient := C.ambient
  ambient_open := C.ambient_open
  i := C.i
  closed := C.closed
  factor := C.factor

/-- The signed Koszul Ext comparison in the very same determinant trivialization.
The chart and codimension equalities retain the entire polynomial presentation;
`HEq` transports only its dependent line-module type. It does not allow an arbitrary
line comparison: `e` is the given system's local comparison. The derived comparison
is fixed on every quotient-augmented Koszul roof by the recorded ordered
contraction formula. Its degree-c homology is the specified Ext comparison.
The atlas's independent restriction and normalized affine-refinement equations,
and the displayed equation with the actual local line comparison, retain the same
Ext comparisons on overlaps rather than choosing new ones after gluing.
Testing affine ambient charts suffices on every affine refinement of an overlap.
All derived categories here use their standard universe, with no size hypothesis.
Source: Stacks, Tags 0BQZ, 0E9Y, 0BZI and 0BZJ
(blueprint: lem-sfb-locnoeth-lci-curve-adjunction-gluing). -/
def FlatLCIAdjunctionSystem.HasNormalizedCurveExtComparisons {X S : Scheme.{u}}
    {p : X ⟶ S} (F : FlatLCIAdjunctionSystem p 1) : Prop :=
  letI : ∀ Z : RingedSpace.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Z)) :=
    fun Z ↦ HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Z))
  letI : ∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
    fun R ↦ HasDerivedCategory.standard (ModuleCat.{u} R)
  letI : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} Z.Modules :=
    fun Z ↦ HasDerivedCategory.standard Z.Modules
  ∀ B : FlatLCIBaseChange p,
    ∃ atlas : PolynomialDualityChartAtlas B.p'
        (((DerivedCategory.singleFunctor.{u + 1} B.X'.Modules 0).obj
          (F.line B))⟦(1 : ℤ)⟧),
      LciKoszulDuality.IsNormalizedAtlas atlas ∧
      ∀ (U : B.X'.Opens) (C : FlatLCIPresentation B.p' 1 U), IsAffine C.P →
        ∃ T : LciKoszulDuality.Chart B.p' 1,
          T.chart = C.polynomialChart ∧ T.c = C.c ∧
          ∃ e : T.line ≅ (Scheme.Modules.tensorPullback T.chart.U.ι).obj (F.line B),
            HEq e (F.localIso B U C) ∧
            ∃ (hI : T.ImageExact)
              (ρ : T.unshiftedModel (atlas.exactData T.chart) ≅ T.unshiftedTarget),
              T.IsNormalized (atlas.exactData T.chart) ρ ∧
              (atlas.identification T.chart).hom ≫
                  (T.shifted (atlas.exactData T.chart) hI ρ).hom =
                T.image.map
                  ((Functor.commShiftIso
                    (Scheme.Modules.restrictFunctor T.chart.U.ι).mapDerivedCategory.{u + 1, u + 1}
                    (1 : ℤ)).hom.app
                      ((DerivedCategory.singleFunctor.{u + 1} B.X'.Modules 0).obj (F.line B)) ≫
                    (shiftFunctor _ (1 : ℤ)).map
                      (((Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
                        (Scheme.Modules.restrictFunctor T.chart.U.ι) 0).hom.app (F.line B)) ≫
                        (DerivedCategory.singleFunctor.{u + 1} _ 0).map
                          (((LciKoszulDuality.openTensorIso T.chart.U.ι).symm.app
                            (F.line B)).hom ≫ e.inv)))

/-- The normalized lci curve adjunction and fundamental class glue over a locally
Noetherian base, retaining the signed Ext comparisons on all affine refinements.
The nodal-datum assertion concerns the identity member; the base-change members
use local regularity along the closed subscheme, not global regularity of pulled
back equations away from it. Thus no Noetherian hypothesis is added on a new base.

Source: Stacks, duality.tex, Tags 0B6V, 0E2Y, 0E9Y, 0E9Z and 0BQZ, assembled
by sheaves.tex, Tags 04TN, 00AL, 00AM and 00AN
(blueprint: lem-sfb-locnoeth-lci-curve-adjunction-gluing).

Proof (the eight steps of the DAG):
1. An affine base open has Noetherian coordinate ring (pqf-lem-affine-open-locnoeth).
Restrict flatness and finite presentation by lem-weil-pbc-flat-morphism-base-change
and lem-weil-pbc-qcqs-morphism-permanence. Refine the given charts by principal
opens of the original affine base; localization preserves the regular sequence.
Omit empty charts. Apply lem-trf-flat-lci-canonical-adjunction in dimension one,
and lem-sfb-lci-curve-fundamental-class, on each affine base open.
2. Their specified base-change comparisons carry the local fundamental maps to
one another and satisfy identity and composition. By
lem-sfb-adjunction-cotangent-determinant-normalization they are the stipulated
cotangent determinant transitions, with the same signs.
3. On an affine W inside a possibly nonaffine intersection V_i intersect V_j,
use c_(V_j,W) inverse composed with c_(V_i,W). Restriction cancels c_(W,Z).
Glue these maps and their inverses by lem-weil-pbc-glue-sheaves-of-modules.
On triple overlaps the middle comparison cancels, giving the cocycle.
4. Glue the lines, their local trivializations, and the fundamental maps by that
same node. Relative differentials restrict by their universal derivation property
(def-sc-relative-differential-sheaf): d(s inverse) = -s inverse squared times ds.
Enlarging the affine cover shows independence of the cover and refinements.
5. Apply the local fundamental-class formula in every additional presentation.
The generator is the sign-adjusted adjunction orientation, with sign
flatLCICurveFundamentalSign c. The signed dual Koszul comparison of
lem-trf-lci-koszul-duality-determinant-comparison fixes the Ext map on every
quotient-augmented roof; its determinant comparison is exactly the same transition.
This supplies the nodal datum, without asserting nodal singularities.
6. On the smooth locus the local fundamental maps are isomorphisms. Their inverses
agree on overlaps and glue. Equality detection proves both inverse equations.
7. For arbitrary S' over S, use the original Noetherian affine theorem's own
base-change comparisons. Do not apply a Noetherian-base theorem to S'. The
presentation-base-change node supplies conormal and differential comparisons,
Koszul exactness and regularity along the pulled-back closed subscheme. Its
determinant comparisons intertwine the old transitions, so the comparison glues.
8. In an ordered Koszul basis all matrices have entries plus or minus f_j.
Coefficient extension preserves those entries, ordered contraction, evaluation
and every fixed sign. Hence the normalized derived comparison, and its Ext
homology, commute with restriction and base change. Uniqueness of its roof
normalization gives the same comparison for every affine refinement. The
adjunction identity/composition laws give all iterated-base-change and family
isomorphism equalities; equality detection descends them from the cover. -/
theorem exists_locnoethLCICurveAdjunctionGluing {X S : Scheme.{u}} (p : X ⟶ S)
    [IsLocallyNoetherian S] [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p]
    (hpure : ∀ s : S, (flatLCIGeometricFibre p s).IsPureDimension 1)
    (hcharts : ∀ x : X, ∃ A : NodalCanonicalPresentation p, x ∈ A.U.1) :
    ∃ F : FlatLCIAdjunctionSystem p 1,
      F.IsNormalized ∧ F.HasNormalizedCurveExtComparisons ∧
      ∃ α : ∀ B : FlatLCIBaseChange p, B.p'.relativeDifferentials ⟶ F.line B,
        F.IsCurveFundamentalClass α ∧
        (∃ D : NodalDualizingDatum p (F.line (FlatLCIBaseChange.identity p)),
          D.fundamental = α (FlatLCIBaseChange.identity p)) ∧
        (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens),
          Smooth (U.ι ≫ B.p') →
            IsIso ((Scheme.Modules.tensorPullback U.ι).map (α B))) ∧
        (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
          (C : FlatLCIPresentation B.p' 1 U),
          C.HasExtIdentification ∧ C.HasDualityModel) ∧
        (∀ (B : FlatLCIBaseChange p) (x : B.X'),
          ∃ U : B.X'.Opens, x ∈ U ∧ Nonempty (FlatLCIPresentation B.p' 1 U)) := by
  sorry

end AlgebraicGeometry
