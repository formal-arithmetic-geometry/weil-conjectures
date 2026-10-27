module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalFibreDimensionOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Relative dimension strata of smooth algebraic spaces

Source: Stacks Project, Tags 0CK5, 02G1, 02G2, 04NS(1), and 0A4J
(blueprint: lem-sfb-smooth-space-dimension-strata).

`T` is the scheme target, viewed over an arbitrary ambient scheme `S`.
The structural case is obtained with `S = T.left` and `T = Over.mk (𝟙 S)`.
Base changes and geometric fibres are the actual presheaf fibre products.
The pullback stratum is the literal subfunctor preimage of the first projection.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smooth algebraic spaces have finite, chart-independent, locally constant relative
fibre dimension. Its clopen open-subspace strata partition the source, commute with every
scheme base change, and have pure geometric fibres when the map is separated and finitely
presented. In the base-change clause the dimension function is `ν ∘ mapPoint (pullback.fst ...)`;
the equality with every chart dimension specifies the same canonical function on the pullback.
Source: Stacks Project, Tags 0CK5, 02G1, 02G2, 04NS(1), and 0A4J
(blueprint: lem-sfb-smooth-space-dimension-strata).

Proof:
1. Smooth charts are locally finitely presented and hence locally of finite type.
   Apply lem-sfb-space-local-fibre-dimension-open to affine charts. Shrink an arbitrary
   chart around its lift to an affine open; lem-sfb-etale-topological-dimension-at-point
   identifies its fibre dimension with that of the original chart. This proves chart
   independence and finiteness, including nonnegativity at every point.
2. On each chart, sbc-lem-smooth-relative-dimension-locally-constant identifies the
   fibre dimension with the locally constant rank of the differentials. The final
   topology of def-a1-space-point-topology descends local constancy to the space.
3. In an atlas, each level set and its complement are invariant opens. Descend them
   with lem-trf-etale-open-chart-morphism-descent. By lem-a1-space-point-open-calculus
   their images are the complementary level sets. Each point has exactly one value.
4. Pull back the atlas using lem-trf-space-fibre-products-etale-covers. Smoothness
   survives base change by lem-sbc-smooth-relative-dimension-permanence and passes
   between charts by lem-sfb-scheme-etale-source-target-properties.
5. Apply lem-sc-fibre-dimension-after-base-change to the pulled-back scheme charts.
   This gives the pointwise dimension formula for every base change, with no algebraicity
   restriction on the residue-field extension.
6. By lem-a1-space-open-factor-scheme-tests the pulled-back open is its subfunctor
   preimage, with the inverse-image point set. The point formula identifies this
   with the new level set; point_open_calculus detects equality of open subfunctors.
7. Under the separation and finite-presentation assumptions a geometric stratum
   fibre is quasi-compact, locally of finite type, and quasi-separated. Quasi-compactness
   is preserved by base change (lem-pc-quasi-compact-base-change) and by passage to a
   clopen subspace. Its diagonal inherits quasi-compactness by base change and restriction.
   Apply lem-sfb-space-component-generic-chart-dimension at each component generic point.
   Its chart dimension is n by steps 1 and 5, and over a field its fibre is the chart itself.
   Thus every component has topological Krull dimension n. Empty fibres have no components. -/
theorem exists_smooth_dimension_strata {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over S) (f : X.obj.obj ⟶ yoneda.obj T)
    (hsmooth : MapToSchemeIsLocally (@Smooth) X T f) :
    ∃ (ν : Point X.obj.obj → ℕ) (A : ℕ → OpenSubspace X),
      (∀ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj), IsEtale a → ∀ v : U.left,
        topologicalKrullDimAt ((yoneda.preimage (a ≫ f)).left.asFiber v) =
          (ν (schemePointMap a v) : WithBot ℕ∞)) ∧
      IsLocallyConstant ν ∧
      (∀ n : ℕ, IsClopen {x | ν x = n} ∧ pointImage (A n).val.ι = {x | ν x = n}) ∧
      (∀ x : Point X.obj.obj, ∃! n : ℕ, x ∈ pointImage (A n).val.ι) ∧
      (∀ (T' : Over S) (h : T' ⟶ T),
        (∀ (U : Over S) (a : yoneda.obj U ⟶ Limits.pullback f (yoneda.map h)), IsEtale a →
          Smooth ((yoneda.preimage (a ≫ pullback.snd f (yoneda.map h))).left) ∧
          ∀ v : U.left,
            topologicalKrullDimAt
              ((yoneda.preimage (a ≫ pullback.snd f (yoneda.map h))).left.asFiber v) =
                (ν (mapPoint (pullback.fst f (yoneda.map h)) (schemePointMap a v)) :
                  WithBot ℕ∞)) ∧
        IsLocallyConstant (ν ∘ mapPoint (pullback.fst f (yoneda.map h))) ∧
        ∀ n : ℕ,
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
            ((A n).val.preimage (pullback.fst f (yoneda.map h))).ι ∧
          IsClopen (pointImage ((A n).val.preimage (pullback.fst f (yoneda.map h))).ι) ∧
          pointImage ((A n).val.preimage (pullback.fst f (yoneda.map h))).ι =
            {x' | ν (mapPoint (pullback.fst f (yoneda.map h)) x') = n}) ∧
      (MapToSchemeIsSeparated X T f →
        MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f →
        MapIsQuasiCompact f → MapIsQuasiCompact (pullback.diagonal f) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T.left) (n : ℕ),
          ∀ C ∈ irreducibleComponents
            (Point (Limits.pullback ((A n).val.ι ≫ f)
              (yoneda.map (Over.homMk (U := Over.mk (g ≫ T.hom)) (V := T) g rfl)))),
            topologicalKrullDim C = (n : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
