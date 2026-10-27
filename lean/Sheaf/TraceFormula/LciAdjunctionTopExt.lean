/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.TraceFormula.LciCoinductionHomComparison
public import Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison
public import Sheaf.AlgebraicGeometry.SheafExt
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Top Ext of a normalized Koszul chart

Source: Stacks Project, duality.tex, Tag 0BQZ, with ambient top-differential coefficients
(blueprint: lem-trf-lci-adjunction-top-ext).
The source uses a single chart U -> P -> S. The existing chart interface also allows
all charts of an lci cover at once. The theorem supplies the family for the normalized
comparison of the dependency; a one-chart cover gives precisely the displayed assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Algebra.CotangentResolution

namespace AlgebraicGeometry.LciKoszulDuality

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]

attribute [local instance] schemeDerived imageRingDerived imageRingInjectives

/-- Invert H^c(rho), after the canonical underlying-Hom and single-complex comparisons.
Its source is the ordinary i_*D_i as an O_P-module, not the derived direct image.
Source: Stacks 0BQZ (blueprint: lem-trf-lci-adjunction-top-ext). -/
def Chart.topExtIso {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} (T : Chart f d)
    (h : PolynomialChartExactData T.chart.i)
    (ρ : T.unshiftedModel h ≅ T.unshiftedTarget) :
    T.scalars.obj T.imageLine ≅
      moduleSheafExt T.chart.P (T.c : ℤ) T.quotientModule T.omega :=
  (((DerivedCategory.homologyFunctor T.chart.P.Modules (T.c : ℤ)).mapIso
      (((coinductionHomComparison T h).app
          ((DerivedCategory.singleFunctor _ 0).obj T.omega)).symm ≪≫
        (T.scalarDerived h).mapIso ρ ≪≫ T.scalarSingle h T.imageLine (T.c : ℤ))) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        T.chart.P.Modules (T.c : ℤ)).app (T.scalars.obj T.imageLine)).symm

/-- The top Ext adjunction is normalized by the actual derived Koszul comparison.
All auxiliary cotangent and determinant inputs are the canonical construction interfaces
of the dependency; no dualizing object, flatness or Noetherian hypothesis is imposed.
For a single immersion take X=U, its top open, f=i followed by the ambient projection,
and d=n-c. The statement below simultaneously supplies the same maps on every chart.
The comparison datum contains normalization for every ordered regular generating sequence
and every ambient-line frame, and the independent open-restriction square. The equation
below therefore specifies those compatibilities for these very top Ext maps.

Source: Stacks Project, duality.tex, Tag 0BQZ
(blueprint: lem-trf-lci-adjunction-top-ext).
Proof:
1. Apply exists_lciKoszulDualityDeterminantComparison unconditionally. For one chart,
n=c+d is the given c<=n, the Koszul regularity is local generation of the actual kernel,
and conormal_free is precisely rank c. No relative dualizing object is needed.
2. Forget the quotient-algebra action using the exact scalar functor. The canonical
homComparison, fixed on K-injective representatives by evaluation at one and projection
onto source degree zero, identifies its source with RHom_P(i_*O_U,Omega^n).
3. Apply H^c. The source is moduleSheafExt by its definition. The target is the single
complex i_*D_i in degree c; singleFunctorCompHomologyFunctorIso identifies its H^c with
i_*D_i, including c=0. The functor preserves the two inverse identities for rho.
Invert this cohomology isomorphism, exactly as in topExtIso. It has the required scale
and sign; no generator or coefficient frame is selected in this construction.
4. The dependency's comparisons are independent of generators and coefficient frames
and satisfy its canonical open-restriction square. Hom-complex projection and ordinary
coinduction evaluation restrict to those same maps on every open. Exact restriction
commutes with kernels, images and quotients, hence with H^c and its single-complex
identification. Apply H^c to the square and invert its horizontal isomorphisms. This
gives the stated open compatibility of these maps; uniqueness follows by their specified
inverse. Empty schemes and zero-rank wedges use the same single-complex formula. -/
theorem exists_lciAdjunctionTopExt
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (C : Coherence.{u}) (κ : Naive.Comparison C) (D : CotangentPresentation.System C)
    (F : CotangentPresentation.AffineIdentifications D)
    (E : CotangentPresentation.LciIdentifications D F κ)
    (_hD : CotangentPresentation.Properties D F κ E)
    (δ : TwoTermPerfectDeterminantData.{u, w}) (_hδ : δ.IsCanonical)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (_cover : ∀ x : X, ∃ T : Chart f d, x ∈ T.chart.U) :
    ∃ (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f)))
      (B : ComparisonData D F κ E f d δ hL),
      ∀ T : Chart f d,
        ∃! α : T.scalars.obj T.imageLine ≅
            moduleSheafExt T.chart.P (T.c : ℤ) T.quotientModule T.omega,
          α.inv = (T.topExtIso (B.atlas.exactData T.chart) (B.rho T)).inv := by
  sorry

end AlgebraicGeometry.LciKoszulDuality
