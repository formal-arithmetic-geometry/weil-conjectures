/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.PurityDncInvariance
public import WeilConjectures.AlgebraicGeometry.DiagonalCounitComparisonData

/-! # Diagonal orientation on an etale coordinate chart

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.md and its proof, Steps 1--4.
(blueprint: det-sp-orientation-charts).

The equality is written for inverse orientations. The coordinate arrow is the actual
ordered affine integration counit mate. The two site comparisons and the exceptional
comparison unit make both sides maps between the same pro-etale objects.

## Main declarations

- `DiagonalOrientationChartsConclusion`: the equality with all canonical transports.
- `diagonalOrientationCharts`: the chart compatibility of the diagonal orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Equality of the restricted inverse diagonal orientation and the coordinate-adjunction
inverse orientation, on the small pro-etale site. All normalized presentations t, D and N
are universally quantified; they are not hypotheses selecting an arbitrary orientation.
The map `OrientationCounit.coordinate` is precisely the two Tate pullbacks, the pullback
of the ordered affine counit mate, exceptional composition with etale locality, and the
comparison induced by the over-Y equation w. Source: blueprint latest, orientation-charts,
statement and proof Steps 3--4 (blueprint: det-sp-orientation-charts). -/
def DiagonalOrientationChartsConclusion (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : (e ≫ (affineTraceAffineSpaceIso Y d).inv) ≫ affineTraceProjection Y d =
      U.ι ≫ f) : Prop :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  letI := isNoetherian_of_locallyOfFiniteType (U.ι ≫ f ≫ aY)
  letI := affineTraceNoetherian Y d
  let v := e ≫ (affineTraceAffineSpaceIso Y d).inv
  letI : IsSeparated (v ≫ affineTraceProjection Y d) :=
    w.symm ▸ inferInstanceAs (IsSeparated (U.ι ≫ f))
  letI : IsSeparated v := IsSeparated.of_comp v (affineTraceProjection Y d)
  ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
    (OrientationRefinement.pull P U.ι).map (P.diagonalDualizingObject d f aY).inv =
      (Dnc.pullComparison P U.ι (P.diagonalTwistEtale X d)).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory.map
            (OrientationCounit.coordinate P d f aY t D N U.toScheme U.ι v w) ≫
        (Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f)).inv ≫
        (OrientationRefinement.pull P U.ι).map (P.diagonalDualizingComparison f).inv

/-- Restriction of the diagonal orientation to an etale coordinate chart equals the
coordinate-adjunction orientation. Source: blueprint latest, orientation-charts,
statement and proof Steps 1--4 (blueprint: det-sp-orientation-charts).

Proof:
1. Apply the defining witness property of `existsUnique_diagonalDualizingObject` to
   `diagonalDualizingObject`. It gives an ordinary-etale orientation o, its coordinate
   counit normalization on every chart, and theta = diagonalDualizingComparison followed
   by nu*(o). Evaluate the normalization at j = U.ι and at e followed by the inverse of
   the canonical ordered-coordinate isomorphism. Finite type gives Noetherianity; the
   over-Y equation gives separatedness of this etale chart map. Cancel the invertible
   source-open exceptional locality. The resulting equation says that pullback of o.inv
   is `OrientationCounit.coordinate`, including both Tate coefficient comparisons.
2. `Dnc.pullComparison`, supplied by `thm-pur-dnc-invariance`, is the composite of the
   exact-functor derived comparisons and the etale/pro-etale inverse-image comparison.
   Naturality at o.inv conjugates nu*(pullback o.inv) to pullback nu*(o.inv).
   Substitute the equation from Step 1 and the presentation equation for theta, then
   use functoriality of composition. This is the displayed inverse-orientation equality.
   Inverting the orientations gives the stated forward equality. No absolute
   separatedness of Y, affineness of U, or positivity of d enters the argument. -/
theorem diagonalOrientationCharts (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : (e ≫ (affineTraceAffineSpaceIso Y d).inv) ≫ affineTraceProjection Y d =
      U.ι ≫ f) :
    P.DiagonalOrientationChartsConclusion d f aY U e w := by
  let := isNoetherian_of_locallyOfFiniteType aY
  let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  let : HasCompactification f := inferInstance
  let := isNoetherian_of_locallyOfFiniteType (U.ι ≫ f ≫ aY)
  let := affineTraceNoetherian Y d
  let v := e ≫ (affineTraceAffineSpaceIso Y d).inv
  let : IsSeparated (v ≫ affineTraceProjection Y d) :=
    w.symm ▸ inferInstanceAs (IsSeparated (U.ι ≫ f))
  let : IsSeparated v := IsSeparated.of_comp v (affineTraceProjection Y d)
  obtain ⟨o, ho, hθ⟩ := (P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec
  intro t D N
  let J := Etale.ordinaryFinitePullback P.Coefficient U.ι
  have hc := ho t D N U.toScheme U.ι v w
  have hcoord : J.map o.inv =
      OrientationCounit.coordinate P d f aY t D N U.toScheme U.ι v w := by
    apply (cancel_mono (P.diagonalEtaleLocality N U.ι f).hom).mp
    simpa only [OrientationCounit.coordinate, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hc
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let ν' := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory
  let L := OrientationRefinement.pull P U.ι
  let η : ν ⋙ L ≅ J ⋙ ν' :=
    Functor.isoWhiskerLeft ν
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ U.ι) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso _ U.ι ≪≫
        Functor.isoWhiskerRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ U.ι).symm ν'
  have hn := η.hom.naturality o.inv
  change L.map (ν.map o.inv) ≫ (Dnc.pullComparison P U.ι _).hom =
    (Dnc.pullComparison P U.ι _).hom ≫ ν'.map (J.map o.inv) at hn
  have hpull : L.map (ν.map o.inv) =
      (Dnc.pullComparison P U.ι (P.diagonalTwistEtale X d)).hom ≫
        ν'.map (J.map o.inv) ≫
        (Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f)).inv := by
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change L.map (P.diagonalDualizingObject d f aY).inv = _
  change P.diagonalDualizingObject d f aY =
    P.diagonalDualizingComparison f ≪≫ ν.mapIso o at hθ
  rw [hθ, Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp, hpull, hcoord]
  simp only [Category.assoc]
  rfl

end WeilConjectures.PurityFiniteSetting
