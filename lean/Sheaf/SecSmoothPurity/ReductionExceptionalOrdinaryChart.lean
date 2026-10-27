/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects

/-! # The ordinary chart transpose calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- In ordinary etale coordinates, the scalar counit equation forces the ordered
chart scalar formula at a single input. Source: blueprint latest, reduction-
exceptional proof, Locality and Charts (blueprint: lem-sp-reduction-ordinary-chart).

Proof: compose the adjunction of open sum/evaluation along i with each of the
specified compact-support adjunctions. The scalar/open counit identity identifies
the restriction of q with the transpose of the scalar-extended composite counit,
postcomposed with a. Transport the two adjunctions by reductionEtaleChartLeftIso.
The chart counit scalar equation for sum followed by ordered affine integration
identifies this transpose with reductionEtaleChartScalarIso, followed by the
chart right functor applied to a. This uses the generator-normalized Tate-line
comparison: both maps send (z tensor x) tensor b to z tensor φ(x)b. The P1
normalizations fix the trace and diagonal classes, and their ordered composites
fix all dimensions. Injectivity of the B-chart adjunction Hom equivalence gives
the equality. Right-adjoint uniqueness is precisely reductionEtaleChartRightIso.
For d=0 the affine adjunction is the identity. The zero coefficient ring is
included by the same generator and adjunction identities. This statement has no
site realization, no intrinsic coefficient transpose and no input-origin choice. -/
theorem reductionExceptional_ordinary_chart
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f)
    (MA : Etale.EtaleCompactSupportNormalization A)
    (MB : Etale.EtaleCompactSupportNormalization B)
    (tA : Etale.OrdinaryFiniteTwistTransport A N hA)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA tA T hT)
    (tB : Etale.OrdinaryFiniteTwistTransport B N hB)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum B N hB tB T hT)
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (GA : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (GB : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X)
    (adjA : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) cf ⊣ GA)
    (adjB : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} B) cf ⊣ GB)
    (L : Etale.DerivedCategoryModule A Y)
    (hL : Etale.DerivedCategory.boundedConstructibleFiniteTor A Y L)
    (LB : Etale.DerivedCategoryModule B Y)
    (a : (Etale.scalarExtension φ Y).obj L ⟶ LB)
    (q : (Etale.scalarExtension φ X).obj (GA.obj L) ⟶ GB.obj LB)
    (hq : (Etale.compactScalarMap φ cf).app (GA.obj L) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) cf).map q ≫
        adjB.counit.app LB = (Etale.scalarExtension φ Y).map (adjA.counit.app L) ≫ a) :
    (Etale.scalarPullbackIso φ i).inv.app (GA.obj L) ≫
        (Etale.ordinaryFinitePullback B i).map q ≫
        (reductionEtaleChartRightIso B MB f i d e he cf GB adjB N hB tB DB hY).hom.app LB =
      (Etale.scalarExtension φ U).map
        ((reductionEtaleChartRightIso A MA f i d e he cf GA adjA N hA tA DA hY).hom.app L) ≫
      (reductionEtaleChartScalarIso φ N hA hB hY d e L).hom ≫
      (Etale.affineTraceRight B N hB Y d ⋙ Etale.ordinaryFinitePullback B e).map a := by
  sorry

end AlgebraicGeometry.ProEtale
