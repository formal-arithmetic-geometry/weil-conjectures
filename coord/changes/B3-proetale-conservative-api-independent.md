# ProEtale localization restriction conservativity: API independence

## Reason

The return rejected two duplicate private conservativity lemmas in
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit`. Reuse their existing library
counterparts. The existing conservativity module imported the legacy lower-shriek API,
which redeclares the same names as this item's finite-coefficient API. Remove that
unnecessary import, spelling out the underlying continuous sheaf pushforward in its two
existing theorem hypotheses. This is definitional unfolding, with identical objects,
morphism types, coefficient universes, hypotheses and conclusions. Neither theorem
requires an inverse-image or lower-shriek construction. The objectwise proof replaces
the legacy evaluation rewrite with `change`.

The changed existing module
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Conservative` is unclaimed
(no coordination lock). It is changed under the explicit unclaimed-module exception,
not as a forced adaptation of a module held by another group. No existing definition,
target statement, or mathematical statement changes. No new theorem names are added.

## Old

The module publicly imported
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`.
In the unchanged context
`(A : Type u') [Category.{u + 1} A] {X : Scheme.{u}}`
and `{G G' : Sheaf (Scheme.ProEt.topology X) A} (φ : G ⟶ G')`:

```lean
lemma ProEtale.isIso_app_of_isIso_localizationRestriction {W : Scheme.{u}} (g : W ⟶ X)
    [WeaklyEtale g]
    (h : IsIso ((ProEtale.localizationRestriction A g inferInstance).map φ))
    (V : X.ProEt) (p : V.left ⟶ W) (hp : p ≫ g = V.hom) :
    IsIso (φ.hom.app (op V))
```

```lean
lemma ProEtale.isIso_of_isIso_localizationRestriction {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, IsIso ((ProEtale.localizationRestriction A (g i) inferInstance).map φ)) :
    IsIso φ
```

## New

Remove the legacy lower-shriek import. Keep the public pro-etale site import; make
`WeilConjectures.Mathlib.CategoryTheory.NatIso` a plain proof-only import and remove the
redundant direct import of `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf`, which the
public site import already exports. With precisely the same section binders, the two theorem
signatures are now:

```lean
lemma ProEtale.isIso_app_of_isIso_localizationRestriction {W : Scheme.{u}} (g : W ⟶ X)
    [WeaklyEtale g]
    (h : IsIso ((Functor.sheafPushforwardContinuous
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)) A (Scheme.ProEt.topology W)
        (Scheme.ProEt.topology X)).map φ))
    (V : X.ProEt) (p : V.left ⟶ W) (hp : p ≫ g = V.hom) :
    IsIso (φ.hom.app (op V))
```

```lean
lemma ProEtale.isIso_of_isIso_localizationRestriction {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, IsIso ((Functor.sheafPushforwardContinuous
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))) A
        (Scheme.ProEt.topology (W i))
        (Scheme.ProEt.topology X)).map φ)) :
    IsIso φ
```

For existing clients, `ProEtale.localizationRestriction A g inferInstance` reduces to
exactly the functor written above. The two original theorem names are retained. The
item removes both private copies and applies the existing second theorem directly.

## Users

`tools/downstream.py` reports the following 240 transitive users. Its declaration-use scan
finds seven external callers of `isIso_of_isIso_localizationRestriction` and no external
caller of the objectwise lemma. The import-pruning checker passes: no downstream source
loses a used declaration through removal of the legacy import. Three callers require an explicit goal-type step immediately after applying conservativity: this
restores the named `localizationRestriction` wrapper expected by their existing rewrites
or instance search. All three are unclaimed. Every existing signature, visibility,
import, and remaining proof line in these callers is unchanged. Four other external
callers compile unchanged against the new theorem; both old theorem types also compile
in the explicit ordinary-API compatibility check.
The sandbox also contains a temporary compatibility check of both original theorem types
against the ordinary API; it is compiled and removed before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Conservative | unclaimed | Unfold restriction in hypotheses; remove legacy import; adapt evaluation step. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit | B3 | Import existing conservativity theorem and remove duplicate helpers. |
| Sheaf.AlgebraicGeometry.AdicClosedImmersionFiniteness | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AbelianIrreducible | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit | unclaimed | Add only `change` to restore restriction wrapper in the local goal. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZero | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom | unclaimed | Add only `change` to restore restriction wrapper in the local goal. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalkPointwise | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TensorPowSection | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClopenIdempotent | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Localization | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Add only a `show` refinement to restore restriction wrapper in the local goal. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.Proper | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.Statement | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Dual | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.DualIrreducible | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FiniteLength | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LisseDuality | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LisseFiltration | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LocalFrobenius | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Stalk | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkCharpoly | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkConstantSheaf | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkFrobenius | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkFunctor | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkIso | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkMonoidal | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkPairing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkUpperStar | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.StalkUpperStarCharpoly | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TraceFunctionVanishing | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.UpperStarExact | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same theorem types up to unfolding restriction; no edit. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same theorem types up to unfolding restriction; no edit. |

The exact original errors and the necessary added proof lines are:

`WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit` (unclaimed):

159:10: failed to synthesize instance of type class `∀ X, IsIso (...)`

```lean
  change IsIso ((localizationRestriction (WeilCoefficients.{u} l) (g i) inferInstance).map
    ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) j).unit.app G))
```

`WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom` (unclaimed):

52:8: Tactic `rewrite` failed: Did not find an occurrence of `(localizationRestriction (WeilCoefficients l) (g i) ...).map 0`

```lean
    change IsIso ((localizationRestriction _ (g i) inferInstance).map (0 : M.X ⟶ M.X))
```

`WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover` (unclaimed):

73:10: failed to synthesize `HasZeroObject (Sheaf (ProEt.topology (U i)) A)`; deterministic timeout at `typeclass` (20000 heartbeats)

```lean
    refine (show IsIso ((ProEtale.localizationRestriction A (U i).ι inferInstance).map
      (0 : F ⟶ 0)) from ?_)
```

## Status

landed 20261015T221610-L-2628303 2026-10-15 (merge of deliver/B3/Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit)

Second reader: all three original callers were compiled independently against the delivered
conservativity module and reproduced the errors above. The OpenCover type refinement avoids
an intermittent unused-`change` warning while providing the same expected type. NatIso is
used only by proofs, so its import is now plain; the direct Sites.Sheaf import is redundant
because the public pro-etale site module already imports it publicly. No declaration is lost
from that latter removal.
