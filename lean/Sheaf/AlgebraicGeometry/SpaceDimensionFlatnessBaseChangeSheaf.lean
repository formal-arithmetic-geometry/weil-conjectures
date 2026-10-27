module

public import Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.BaseChangeResidueTranscendenceLifts
import Sheaf.AlgebraicGeometry.PointwiseModuleFlatnessBaseChange

/-! # Dimension-filtered flatness, base change and the fpqc sheaf condition

Source: Stacks Project, Flatness on Spaces, Tags 0CWS, 0CWT and 0CWW(1)
(blueprint: lem-sfb-space-dimension-flatness-base-change-sheaf).

The cutoff uses the actual residue-field map and the actual module stalk on every
representable etale scheme chart. All base changes are the existing sheaf fibre products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The landed cutoff criterion restricted to one specified etale chart.
The chart map, tensor pullback and scalar actions are those of dimensionFlatCondition.
Source: Stacks Project, Tag 0CWS, equivalence of the one-atlas and all-chart criteria
(blueprint: lem-sfb-space-dimension-flatness-base-change-sheaf). -/
def dimensionFlatAtlasCondition {S : Scheme.{u}} {Y B : Over S}
    {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y) (M : X.Modules) (n : ℕ)
    (g : B ⟶ Y) (U : (enlargedFibreProduct f (dimensionFlatBaseMap g)).EtaleSite) : Prop :=
  ∀ (x : (enlargedFibreProduct f (dimensionFlatBaseMap g)).etaleForget.obj U),
    (n : Cardinal.{u}) ≤
      @Algebra.trdeg (B.left.residueField ((dimensionFlatChartMap f g U).left x))
        (((enlargedFibreProduct f (dimensionFlatBaseMap g)).etaleForget.obj U).residueField x)
        _ _ (((dimensionFlatChartMap f g U).left).residueFieldMap x).hom.toAlgebra →
    Module.Flat (B.left.presheaf.stalk ((dimensionFlatChartMap f g U).left x))
      ((ModuleCat.restrictScalars (((dimensionFlatChartMap f g U).left).stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor
          ((enlargedFibreProduct f (dimensionFlatBaseMap g)).etaleForget.obj U).toRingedSpace
          x).obj
          ((schemeRestriction (enlargedFibreProduct f (dimensionFlatBaseMap g)) U).obj
            ((moduleTensorPullback (enlargedFibreProductFst f (dimensionFlatBaseMap g))).obj
              M))))


/-- Dimension-filtered flatness is stable under all scheme base changes, descends for
every fpqc covering, can be checked on any single surjective etale atlas, and gives
the fpqc sheaf of morphisms to Y satisfying the cutoff. The equivalences specify its
values and the last equation specifies restriction by composition, on every section.

Source: Stacks Project, Tags 0CWS, 0CWT and 0CWW(1)
(blueprint: lem-sfb-space-dimension-flatness-base-change-sheaf).

Proof:
1. Fix a surjective etale scheme atlas of X. Compare it with any other chart after
   base change using lem-trf-space-fibre-products-etale-covers. The two etale projections
   have finite separable residue extensions by
   lem-weil-pbc-etale-fibre-discrete-separable-points. The transcendence-degree tower
   equality (lem-kun-transcendence-degree-tower) preserves the cutoff, and
   lem-sfb-space-module-flat-point-chart-independence preserves pointwise base-flatness.
   Thus testing on any one atlas is equivalent to testing on all charts.
2. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence on this atlas. Its
   tensor pullbacks agree with restriction of the algebraic-space pullbacks. Tensor
   associativity identifies repeated pullbacks by (r tensor m) tensor s -> rs tensor m,
   with inverse s tensor m -> (1 tensor m) tensor s. Finite algebra generators and
   module generators remain generators after tensor base change. Thus the chart
   morphisms remain locally finite type, with finite type pulled-back coefficients.
3. For any further base change and a chart point above the cutoff,
   lem-sfb-scheme-base-change-residue-transcendence-lifts gives at least that residue
   transcendence degree at its old image. Apply the assumed flatness there and ascent
   in lem-sfb-pointwise-module-flatness-base-change. Step 1 gives the all-chart criterion.
4. For an fpqc covering, lift the base point to a covering member. The equality-lift
   clause of lem-sfb-scheme-base-change-residue-transcendence-lifts supplies a point
   upstairs with exactly the old residue transcendence degree. Local flatness on that
   member descends by the flat-base reflection clause of
   lem-sfb-pointwise-module-flatness-base-change. Step 1 gives the downstairs criterion;
   the reverse direction is step 3.
5. Step 3 gives restrictions by composition, with identity and composition laws from
   tensor associativity. On the relative site values are singleton or empty. Step 4
   gives existence of the glued section and subterminality gives uniqueness. Equivalently,
   for the absolute subfunctor of Y, lem-weil-pbc-fpqc-representable-descent glues the
   compatible morphisms to Y, and step 4 verifies their cutoff condition. On an empty
   test scheme the pointwise criterion is vacuous and its unique section is retained. -/
theorem dimensionFlat_baseChange_fpqc_atlas_sheaf
    {Y : Over (Spec (.of (ULift.{u} ℤ)))}
    {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (f : X ⟶ schemeSpace Y) (hf : MapIsLocally (@LocallyOfFiniteType) f)
    (M : X.Modules) (hMqc : M.IsQuasicoherent) (hMft : M.IsFiniteType) (n : ℕ) :
    (∀ (B B' : Over (Spec (.of (ULift.{u} ℤ)))) (g : B ⟶ Y) (h : B' ⟶ B),
      dimensionFlatCondition f M n g → dimensionFlatCondition f M n (h ≫ g)) ∧
    (∀ (I : Type w) (B : Over (Spec (.of (ULift.{u} ℤ)))) (b : B ⟶ Y)
      (Bᵢ : I → Over (Spec (.of (ULift.{u} ℤ)))) (g : ∀ i : I, Bᵢ i ⟶ B),
      Presieve.ofArrows (fun i ↦ (Bᵢ i).left) (fun i ↦ (g i).left) ∈
        Scheme.fpqcPrecoverage B.left →
      (dimensionFlatCondition f M n b ↔
        ∀ i : I, dimensionFlatCondition f M n (g i ≫ b))) ∧
    (∀ (B : Over (Spec (.of (ULift.{u} ℤ)))) (g : B ⟶ Y)
      (U : (enlargedFibreProduct f (dimensionFlatBaseMap g)).EtaleSite),
      IsSurjective U.obj.hom →
      (dimensionFlatCondition f M n g ↔ dimensionFlatAtlasCondition f M n g U)) ∧
    ∃ (F : Sheaf (Scheme.fpqcTopology.over (Spec (.of (ULift.{u} ℤ)))) (Type (u + 1)))
      (e : ∀ B : Over (Spec (.of (ULift.{u} ℤ))),
        F.obj.obj (op B) ≃ {b : B ⟶ Y // dimensionFlatCondition f M n b}),
      ∀ (B B' : Over (Spec (.of (ULift.{u} ℤ)))) (g : B' ⟶ B) (s : F.obj.obj (op B)),
        (e B' (F.obj.map g.op s)).val = g ≫ (e B s).val := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
