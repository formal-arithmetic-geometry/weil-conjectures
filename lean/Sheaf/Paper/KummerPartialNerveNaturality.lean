/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KummerPartialNerveScalarMorphism
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.Paper.PartialKummerBoundaryUnitModel
public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.Paper.KummerParameterizedTerm
public import Sheaf.Paper.KummerNerveCoordinates
public import Sheaf.Paper.KummerChartGeometryMaps
public import Sheaf.Paper.KummerNormalizedChart
public import Sheaf.Paper.KummerRefinement
public import Sheaf.Paper.KummerCoefficientModels
import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.AlgebraicGeometry.SNCFiniteFibreClassification
import Sheaf.Paper.RootTowerLisseMorphismExtension
import Sheaf.Paper.RootTowerPunctureInvariance
import Sheaf.Paper.RootTowerBoundaryAcyclicity
import Sheaf.CategoryTheory.DerivedCechImageTotalization
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization

/-! # Successive Kummer roots and puncture-map naturality
Source: main-20261015 direct-image stability proof paragraph (3), agent expansion;
exact all-continuous geometric reference WANTED.
(blueprint: lem-sfb-kummer-partial-nerve-naturality).

## Main statements

* `ChartPair`: simultaneous actual root-chart data for both modules and fields.
* `kummer_partial_nerve_naturality`: existence of a covering by these normalized charts.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.KummerPartialNerve
open Profinite.CondensedAction
/-- Simultaneous extension, morphism and successive-nerve data on a single chart.
The matrix is E-linear and equivariant; its condensations use exactly the same
matrix over E and Omega. Both extension squares use the actual pullback of f.
Source: direct-image proof (3), all chartwise conclusions
(blueprint: lem-sfb-kummer-partial-nerve-naturality). -/
structure ChartPair (p ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {Y : Scheme.{u}} {A : Type u} [Finite A] [DecidableEq A]
    (D : Y.IdealSheafData) (C : A → Y.IdealSheafData) (Jo Ji J : Finset A)
    (L L' : PartialKummer.SchemeModules (fieldRing E.1).X (tameBoundaryOpen D).toScheme)
    (f : L ⟶ L') where
  chart : TameRootExtensionChart C J
  geometry : TameRootChartGeometry p D chart
  split : DeckSplit p Jo Ji J
  successive : SuccessiveRoots p J chart.parameters Ji
  boundary : chart.boundary ⟶ chart.tower p
  boundary_over : boundary ≫ chart.towerMap p = chart.boundaryToBase
  roots_zero : ∀ n a, boundary.appTop (fullParameterRootSection p chart.parameters n a) = 0
  representation : PartialKummer.FiniteRepresentation E.1
    (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji})
  representation' : PartialKummer.FiniteRepresentation E.1
    (ParameterRootDeckGroup p {a : A // a ∈ Jo} ×
      ParameterRootDeckGroup p {a : A // a ∈ Ji})
  [environmentE : Environment (fieldRing E.1)
    (ParameterRootDeckGroup p {a : A // a ∈ Jo})
    (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
  [environmentOmega : Environment (fieldRing (PadicAlgCl ℓ))
    (ParameterRootDeckGroup p {a : A // a ∈ Jo})
    (ParameterRootDeckGroup p {a : A // a ∈ Ji})]
  finite : FieldChart D chart split geometry representation E.1 (RingHom.id E.1)
    L boundary boundary_over
  finite' : FieldChart D chart split geometry representation' E.1 (RingHom.id E.1)
    L' boundary boundary_over
  closure : FieldChart D chart split geometry representation (PadicAlgCl ℓ) E.1.subtype
    ((extendToClosure ℓ E _).obj L) boundary boundary_over
  closure' : FieldChart D chart split geometry representation' (PadicAlgCl ℓ) E.1.subtype
    ((extendToClosure ℓ E _).obj L') boundary boundary_over
  maps : MorphismData D chart split geometry ℓ E L L' f boundary boundary_over
    finite finite' closure closure'

/-- Successive Kummer root nerves, the normalized composite-adjunction comparison,
and naturality for an actual morphism of strict-local Kummer-tame lisse modules.
Source: blueprint main-20261015, direct-image stability proof paragraph (3), extracted
successive-root-nerve argument; exact all-continuous geometric reference WANTED.
(blueprint: lem-sfb-kummer-partial-nerve-naturality).

Proof, following the fourteen DAG steps:
1. Use lem-sfb-snc-universal-residual-charts on J for common connected affine charts
and their connected strict-local root towers; their geometry is independent of L.
Apply lem-sfb-tame-integral-reduction-family to L and L' on those same charts.
2. Apply lem-sfb-snc-tame-finite-fibre-classification and
lem-sfb-equivariant-adic-fibre-realization to their compatible finite quotients,
retaining the actual root-deck descent actions and the common full root tower.
3. Define both extensions by point pullback of their continuous-function modules.
A finite basis makes them lisse. Their restrictions and boundary maps are the
specified identifications. Ordinary scalar extension gives the Omega models.
4. Use lem-sfb-root-tower-lisse-morphism-extension to extend f uniquely. By
lem-weil-pbc-condensed-field-continuous-realization its matrix entries are continuous
functions on the connected full tower, hence constant in the totally disconnected E.
5. Apply lem-sfb-root-tower-profinite-base-change and restriction injectivity to the
two equivariance composites on every full profinite parameter object.
6. Uniqueness gives restriction compatibility and identity-restricting isomorphisms.
For Omega also use lem-sfb-root-tower-puncture-invariance and derived adjunction.
7. The disjoint-root algebra presentation gives SuccessiveRoots, fixing coefficients
and every root. Cofinality of diagonal orders follows from prime-to-p least common
multiples. Use lem-sfb-compatible-kummer-tower-cech for both partial towers.
8. The torsor coordinates (x,g) to (x,gx) give DoubleNerve with its specified faces,
degeneracies and diagonal. Moving the first vertex acts on the coefficient.
9. Use lem-sfb-root-tower-boundary-acyclicity for every profinite parameter and
lem-sfb-derived-cech-image-totalization for coherent nonnegative resolutions,
including all actual restriction-of-sections augmentations.
10. Apply lem-sfb-condensed-product-bar-comparison with inner invariants first.
Its total sign is d_o + (-1)^a d_i + (-1)^(a+b) d_resolution.
11. Apply lem-sfb-derived-composition-adjunction-normalization: the augmentation
comparison is the specified conjugate theta, including its units and counits.
12. The actual extended matrix map gives both geometric-nerve maps. Naturality of
the normalized comparisons and every injective-resolution lift gives arrow naturality.
Uniqueness identifies restricted extension maps on further common refinements.
13. Repeat the same constructions over Omega on the same charts using ordinary
finite-basis scalar extension; no direct image is commuted with scalar extension.
14. The empty stratum has an empty cover. Trivial outer group uses its constant
unnormalized nerve. The zero representation and rank-zero modules are retained.
-/
theorem kummer_partial_nerve_naturality
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (_hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D)
    (Jo Ji : Finset (Fin hD.2.2.choose)) (_hdisjoint : Disjoint Jo Ji) (_hJi : Ji.Nonempty)
    (L L' : PartialKummer.SchemeModules (fieldRing E.1).X (tameBoundaryOpen D).toScheme)
    (_hL : IsLisseCoefficientModule (fieldRing E.1).X L)
    (_hL' : IsLisseCoefficientModule (fieldRing E.1).X L')
    (_htame : IsStrictLocalKummerTameModule p (fieldRing E.1).X D (tameBoundaryOpen D).ι L)
    (_htame' : IsStrictLocalKummerTameModule p (fieldRing E.1).X D (tameBoundaryOpen D).ι L')
    (f : L ⟶ L') :
    ∃ (I : Type u)
      (models : I → ChartPair p ℓ E D (kummerComponents D hD)
        (kummerIndices D hD Jo) (kummerIndices D hD Ji)
        (kummerIndices D hD (Jo ∪ Ji)) L L' f),
      Presieve.ofArrows (fun a ↦ (models a).chart.boundary)
        (fun a ↦ (models a).chart.boundaryToStratum) ∈
          Scheme.proetalePrecoverage
            (ParameterStratum (kummerComponents D hD) (kummerIndices D hD (Jo ∪ Ji))) := by
  sorry

end AlgebraicGeometry.ProEtale.KummerPartialNerve
