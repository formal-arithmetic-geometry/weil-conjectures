module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.Paper.PurityDncInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.ProjectionPurityAgreement

/-! # Diagonal orientation on an open coordinate chart

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.md
(blueprint: det-sp-orientation-charts).

The equality is between inverse orientations on the actual small pro-etale site.
The affine arrow is the published ordered integration counit mate. The coordinate
map to Mathlib's affine space is read in the canonically isomorphic ordered tower.

## Main declarations

- `DiagonalOrientationChartsConclusion`: the equality of the specified pro-etale arrows.
- `diagonalOrientationCharts`: compatibility of diagonal orientation with coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate-adjunction equality, with all source, twist and site comparisons
written out. The equality for inverse arrows is equivalent to the orientation
comparison because the diagonal orientation and all comparison arrows are invertible.
The input `w` is precisely the assertion that the coordinate map is over Y, read
through the canonical ordered-coordinate isomorphism. The normalized presentations
`t`, `D` and `N` are universally quantified, as in DiagonalOrientationNormalization;
no independent orientation or comparison map is an input.
Source: blueprint diagonal orientation on a coordinate chart, displayed equality
(blueprint: det-sp-orientation-charts). -/
def DiagonalOrientationChartsConclusion (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : (e ≫ (affineTraceAffineSpaceIso Y d).inv) ≫ affineTraceProjection Y d = U.ι ≫ f) :
    Prop :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian Y d
  let v := e ≫ (affineTraceAffineSpaceIso Y d).inv
  letI : IsSeparated (v ≫ affineTraceProjection Y d) :=
    w.symm ▸ inferInstanceAs (IsSeparated (U.ι ≫ f))
  letI := IsSeparated.of_comp v (affineTraceProjection Y d)
  letI : HasCompactification f := inferInstance
  letI : HasCompactification (U.ι ≫ f) := inferInstance
  letI : HasCompactification (v ≫ affineTraceProjection Y d) := inferInstance
  ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.map
        (P.diagonalDualizingObject d f aY).inv =
      (Dnc.pullComparison P U.ι (P.diagonalTwistEtale X d)).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory.map
          ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
              P.diagonalExponent_annihilates t U.ι
              (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
            (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
              P.diagonalExponent_annihilates t v
              (affineTraceInvertible P.diagonalExponent Y
                (P.diagonalExponent_isUnit aY) d) d).inv ≫
            (Etale.ordinaryFinitePullback P.Coefficient v).map
              (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) ≫
            (P.diagonalEtaleLocality N v (affineTraceProjection Y d)).hom ≫
            (P.diagonalDualizingCongr w).hom ≫
            (P.diagonalEtaleLocality N U.ι f).inv) ≫
        (Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f)).inv ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.map
          (P.diagonalDualizingComparison f).inv

/-- Restriction of the diagonal orientation agrees with the coordinate-adjunction
orientation. The bottom intermediate field expresses E = Q_l. The fixed setting
supplies the algebraic closure of F_q, l different from its characteristic, and
n >= 1. No absolute separatedness of Y is required.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.md
(blueprint: det-sp-orientation-charts).

Proof:
1. The defining existence-and-uniqueness theorem for diagonalDualizingObject
   supplies its ordinary presentation o, its DiagonalOrientationNormalization,
   and the equation identifying the pro-etale orientation with that presentation.
2. Apply the normalization to j = U.ι and to the given etale coordinate map,
   read through the canonical affine-space/tower isomorphism. Cancel the open
   exceptional-locality isomorphism on the right.
3. Naturality of the canonical derived pullback/site comparison transports
   the resulting equality to the pro-etale site. Substitute the presentation
   equation and expand functoriality of composition. The result is the displayed
   equality of inverse arrows, with every comparison map retained.
This uses no absolute separatedness or affineness assumption, and also applies
when U is empty or d = 0. -/
theorem diagonalOrientationCharts (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥) {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : (e ≫ (affineTraceAffineSpaceIso Y d).inv) ≫ affineTraceProjection Y d = U.ι ≫ f) :
    P.DiagonalOrientationChartsConclusion d f aY U e w := by
  let := isNoetherian_of_locallyOfFiniteType aY
  let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  let := isNoetherian_of_locallyOfFiniteType U.ι
  let := affineTraceNoetherian Y d
  let v := e ≫ (affineTraceAffineSpaceIso Y d).inv
  let : Etale v := inferInstance
  let : IsSeparated (v ≫ affineTraceProjection Y d) :=
    w.symm ▸ inferInstanceAs (IsSeparated (U.ι ≫ f))
  let := IsSeparated.of_comp v (affineTraceProjection Y d)
  let : HasCompactification f := inferInstance
  let : HasCompactification (U.ι ≫ f) := inferInstance
  let : HasCompactification (v ≫ affineTraceProjection Y d) := inferInstance
  obtain ⟨o, ho, hθ⟩ := (P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec
  intro t D N
  have hn := ho t D N U.toScheme U.ι v w
  have hn' := congrArg (fun k ↦ k ≫ (P.diagonalEtaleLocality N U.ι f).inv) hn
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hn'
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let νU := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory
  let L := (ProEtale.upperStar
    (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor
  let η : ν ⋙ L ≅ Etale.ordinaryFinitePullback P.Coefficient U.ι ⋙ νU :=
    Functor.isoWhiskerLeft ν (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ U.ι) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso _ U.ι ≪≫
        Functor.isoWhiskerRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ U.ι).symm νU
  have hnat := η.hom.naturality o.inv
  change L.map (ν.map o.inv) ≫
      (Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f)).hom =
    (Dnc.pullComparison P U.ι (P.diagonalTwistEtale X d)).hom ≫
      νU.map ((Etale.ordinaryFinitePullback P.Coefficient U.ι).map o.inv) at hnat
  have hnat' := congrArg
    (fun k ↦ k ≫ (Dnc.pullComparison P U.ι (P.diagonalOrdinaryDualizing f)).inv) hnat
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hnat'
  change L.map (P.diagonalDualizingObject d f aY).inv = _
  change P.diagonalDualizingObject d f aY = _ at hθ
  rw [hθ]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp]
  rw [hnat', hn']
  simp only [Functor.map_comp, Category.assoc]
  rfl

end WeilConjectures.PurityFiniteSetting
