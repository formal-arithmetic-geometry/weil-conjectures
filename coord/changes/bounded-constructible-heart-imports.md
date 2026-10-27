# Heart-level coefficient data and scalar-extension API

## Reason

The original isTriangulated_boundedConstructible instance can be proved from the existing
constructible Serre arguments. Their original imports, however, went back through the very
bounded-derived module being proved: continuous integral data imported it to define only
integralConstructible, and finite-discrete encodings imported a bounded realization module
to obtain ordinary category abbreviations. IntegralConstructibleKernels additionally imported
the bounded scalar-extension result only for its proved heart-level private helpers.
Factoring these dependency edges is necessary to use the existing complete proofs without
an import cycle. This is not a division motivated by a compiler time limit.

No mathematical definition, target, existing public signature or persistent attribute changes.
The existing private lfp_extend is promoted to public in the lower Sheaf module so that
heart-level consumers can import it without importing bounded-derived categories.
All relocated public declarations retain their original names and bodies. The original
modules reexport them publicly, preserving the existing API. The source module's original
public imports and non-theorem bodies stay verbatim. All adapted Sheaf modules were unclaimed
when checked; this delivery does not adapt a module held by another group.

## Old

ContinuousIntegralCoefficients publicly imported
WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory and defined all coefficient
data together with this unchanged declaration:

```lean
noncomputable abbrev integralConstructible (X : Scheme.{u}) :=
  ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)
```

FiniteDiscreteRealizationFunctor defined the following ordinary categories and additive instance
alongside the bounded realization interface:

```lean
abbrev FiniteDiscreteInternalModules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)

abbrev FiniteDiscreteEtalePlus (T : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} B)))

abbrev FiniteDiscreteProEtaleSheaves (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B))

noncomputable instance finiteDiscreteEncoding_additive : E.functor.Additive :=
  Functor.additive_of_preserves_binary_products _
```

FiniteDiscreteCoefficientEncoding publicly imported FiniteDiscreteRealizationFunctor.
Its two encoding definitions were already complete and are not mathematically changed.
IntegralConstructibleKernels imported all BoundedConstructibleExtendScalars for
pullbackExtendScalarsIso and lfp_extend, although it only uses their heart-level content.

The scalar-extension module originally declared the following signatures (inside its
existing R, S, phi and scheme variable context):

```lean
lemma fp_iff_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) : Mod.IsFinitelyPresented R M ↔ Mod.IsFinitelyPresented R N

lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M)

omit [IsCommMonObj S] in
lemma fp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M)

omit [IsCommMonObj S] in
private lemma lfp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented S ((Mod.extendScalars φ).obj M)
```

## New

ContinuousIntegralCoefficientData contains the identical coefficient data, proofs and attributes,
with the bounded category alias excluded. ContinuousIntegralCoefficients publicly imports it and
the same source DerivedCategory module and keeps integralConstructible exactly as displayed above.
IntegralScalarContractive, ContinuousCoefficientRealizations, IntegralMatrixPivotCover,
IntegralConstructibleKernels and IntegralConstructibleSerre now import the data module.

FiniteDiscreteModuleCategories contains exactly the four displayed declarations with their
original signatures and bodies. FiniteDiscreteRealizationFunctor publicly imports this module,
retains all original imports and keeps every other declaration unchanged.
FiniteDiscreteCoefficientEncodingData contains both original encoding definitions verbatim.
FiniteDiscreteCoefficientEncoding publicly imports it and the original realization module.
FiniteDiscreteRestrictionEncoding, FiniteDiscreteEncodedPresentation,
FiniteDiscreteConstructibleLocalPiece and FiniteDiscreteConstructibleEncoding import the data
module instead. Thus heart-level finite-discrete proofs do not depend on bounded realization.

PullbackExtendScalarsComparison contains the existing constructive adjunction proof, now as
pullbackExtendScalarsComparison. The original private pullbackExtendScalarsIso keeps its
signature and its original body verbatim (reviewer FIX, 2026-10-24): Sheaf.Paper.CondensedLocalModelGluing
imports BoundedConstructibleExtendScalars with `import all` and unfolds that body (`exact huniq` in
local_adjoint), which fails when the body is replaced by the irreducible comparison. LocallyFinitelyPresentedExtendScalars is now the single
defining module of the existing fp_iff_of_iso, fp_map, fp_extend and lfp_extend declarations.
BoundedConstructibleExtendScalars publicly imports it, with no duplicate declarations or
wrappers for these four results. The three formerly public theorems keep their names,
signatures and bodies; lfp_extend is promoted from private to public with its original
signature and full finite-presentation proof. Its comparison reference uses the new lower
comparison. IntegralConstructibleKernels imports and uses lfp_extend directly, without a
renamed locallyFinitelyPresented_extendScalars duplicate. This is the concrete repair of
the c51089c9b duplicate-statement return.

The comparison isomorphisms are irreducible and used through their standard Iso/NatIso API.
IntegralConstructibleKernels also caches additive/exact pullback-functor instances, keeps scalar
extension locally irreducible, and transports the equality of kernel maps with kernelIsoOfEq
instead of rewriting inside the large local finite-presentation predicate. A private generic
map_pullback_section helper proves the section equation once before specializing to the
nested module pullbacks. The two cokernel comparison isomorphisms are abstracted together
with their defining equations, preserving their original constructions. Profiling identified
typeclass search and that rewrite as significant costs. These optimizations preserve all
signatures and constructions; no proof or module is divided to meet the compile limit.
The private isomorphism users in IntegralMatrixKernelLocallyFree,
IntegralLfpLocallyFreeResolution and IntegralLfpLocalTorsionCharts use the unchanged Iso API.

FiniteDiscreteConstructibleKernels adds the proved kernel closure required for the finite-torsion
constructor. Its private reverse finite-presentation helpers are relocated from
FiniteDiscreteConstructibleModel, which imports the kernel module with private access.
The five original private declarations regularHomEquiv, scalarRegularIso, encodedConstantFP,
internalLisseFP and internalComparisonConstructible now have exactly one defining module.
The existing public model theorem, its signature and its complete proof remain verbatim.
The model drops its now-unused private import of FiniteDiscreteEncodedPresentation.

EllAdicBoundedTriangulated specializes the newly proved source finiteness-coefficient instance,
with the unit-ball instance supplied explicitly. Its duplicate private continuous_lf and
triangulated_of_serre copies are removed. All existing public imports and the public theorem
signature are preserved. The now-unused private imports of ProEtaleModuleConstructiblePullback,
CondensedConstructibleSerre and IntegralConstructibleSerre are removed; the source theorem
already packages their argument. Both additional Sheaf modules are unclaimed.

No meaning of a target definition changes, so no target statement review is reopened by this
factorization. Existing node statements and unit routes are unchanged. Lean attachments follow
the relocated declarations, and the integral and scalar-extension proof dependencies name the
new lower helpers. Four new nodes record the two helpers, finite-discrete kernel closure
and the relocated ordinary category abbreviations. The current canonical node
lem-sfb-bounded-constructible-triangulated-finiteness records the existing coefficient instance
and its complete Serre-to-derived proof; no duplicate instance node is introduced.

The integral-kernel proof also uses local irreducibility of upperStarFromPoint,
upperStarFromPointComp and their monoidal and braided instances, preventing repeated
unfolding of the point inverse-image construction. Its generic private equation helpers
and abstracted presentation isomorphisms preserve the argument while reducing elaboration.
The complete module compiled in 33.7 seconds after this change.
FiniteDiscreteRealizationFunctor uses the same local point-inverse-image transparency
settings and was recompiled successfully. All such attributes are local;
existing public declaration signatures and persistent attributes remain unchanged.
Two private semireducible monoid-structure caches avoid re-expanding the monoidal
coefficient and pullback constructions during repeated instance comparisons. Their
class-definition warning setting is scoped to the caches and their local registration.
The complete kernel module compiled in 42.1 seconds with these caches.

The new scalar-extension signatures are exactly the four displayed in Old, with
`private lemma lfp_extend` replaced by `lemma lfp_extend`; each now lives in
LocallyFinitelyPresentedExtendScalars. The original module publicly reexports them.

## Users

The following table combines the downstream declaration-use audit with every adapted and new
module. The audit uses tools/downstream.py's source-index and whole-word matching method, with
all relocated continuous declarations, all four category declarations, both encoding declarations,
both scalar helpers, the anonymous IsMonHom instances of the two integral coefficient maps,
and the local EssentiallySmall instance for Profinite. The six consumers named by the
2026-10-22 return are explicitly included below. The six additional consumers returned at
02fb5a587 and seven newer matches are included after a fresh audit of current shared sources;
none of these thirteen added consumers is currently claimed.
Such a source audit overapproximates uses. Every unchanged consumer sees
the identical API through its original imports; consumers in the heart-level dependency chain
are the explicit adaptations described above. Holder names are read from current claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars | unclaimed | Publicly reexport the relocated fp_iff_of_iso, fp_map, fp_extend and lfp_extend; retain the derived theorem. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated | unclaimed | Apply the proved source instance for each ell-adic constructor; remove two duplicate private helpers and three unused private imports. Public signature unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars | unclaimed | New lower module; proved helper or identical relocated declarations. |
| Sheaf.AlgebraicGeometry.PullbackExtendScalarsComparison | unclaimed | New lower module; proved helper or identical relocated declarations. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.CompletedCondensedCoefficients | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousFiniteEtaleTraceLattice | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralCoefficientData | unclaimed | New lower module; proved helper or identical relocated declarations. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | Public reexport of coefficient data; retain integralConstructible verbatim. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralDerivedUnit | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteComparisonPresentation | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Public reexport of the identical encoding and its old imports. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncodingData | unclaimed | New lower module; proved helper or identical relocated declarations. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleKernels | unclaimed | New lower module; proved helper or identical relocated declarations. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | Import the relocated private presentation helpers from FiniteDiscreteConstructibleKernels; remove their five duplicate local definitions. Public theorem and its proof unchanged. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.FiniteDiscreteModuleCategories | unclaimed | New lower module; proved helper or identical relocated declarations. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Publicly import the identical category abbreviations/additive instance. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralConstantModelLocalResolution | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Use lower coefficient data and scalar-extension helpers; statement unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralHeartLocalModel | Z9 | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralLocalizationHomColimit | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralModels | U6 | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueComparisonInterface | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueOrdinaryRestrictPullComp | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullFlatModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullFlatModelComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullOrdinaryUnit | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullSquare | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullSquareComp | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullSquareData | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResiduePullbackPreservesFlat | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueRestrictPullComp | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorRouteDescent | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Import lower coefficient data instead of the bounded-derived wrapper; APIs unchanged. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.LisseLatticeReducedOpen | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.SpectralEtaleLocalLattices | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.SpectralFiniteEtaleTraceLattice | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | F4 | Fill the existing instance proof; add private proof imports/helpers.  |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Same declaration names, signatures and bodies, available through original public reexports. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Audited for both integral-map IsMonHom instances and the local Profinite EssentiallySmall instance; original imports and statements are unchanged, with identical relocated data reexported. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Audited for both integral-map IsMonHom instances; original imports and statements are unchanged, with identical map instances reexported. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Uses integralScalarExtension and was audited for the local Profinite EssentiallySmall instance; the functor retains its name, signature and body through the original public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Audited for the local Profinite EssentiallySmall instance; it remains local to the encoding construction, and this consumer needs no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Audited for the local Profinite EssentiallySmall instance; it remains local to the encoding construction, and this consumer needs no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Audited for the local Profinite EssentiallySmall instance; it remains local to the encoding construction, and this consumer needs no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | U7 | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ContinuousAdicProperBaseChangeRestriction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | U4 | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteDiscreteScalarConstantModels | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.P1CounitScalar | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | T5 | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Q3 | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Textual instance-use audit; integral-map instances retain identical statements and bodies through the public data reexport. No adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Textual local-instance audit overapproximates uses; relocated encoding instances remain local with identical bodies. No importer-visible instance is removed; no adaptation. |

| Sheaf.Paper.ContinuousScalarDerivedEncoding | V8 | Uses integralScalarMap and integralScalarExtension; their names, signatures, bodies and IsMonHom instances are preserved by the original public reexport. No adaptation. |

| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | Textual local-instance audit overapproximates uses; the Profinite EssentiallySmall instance remains local to the encoding construction with its identical body. No adaptation. |

| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Textual match for the local Profinite EssentiallySmall instance. The relocated instance stays local with the identical body; this consumer uses the existing site and scalar APIs unchanged. No adaptation. |

| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Textual match for the local Profinite EssentiallySmall instance. The relocated instance stays local with the identical body; existing coefficient and derived-category APIs are unchanged. No adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Textual local-instance audit overapproximates uses. The Profinite EssentiallySmall instance stays local with the identical body; no importer-visible instance or Hom-chain API changes. No adaptation. |

| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.CoefficientHeart | C6 | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Uses the preserved integral coefficient API or its map instances; identical names, signatures and bodies are publicly reexported. No adaptation. |
| Sheaf.Paper.CompleteIntegralResidueFunctor | T2 | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | E6 | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | H5 | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | V1 | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | N1 | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Textual local-instance match; the encoding instances remain local with identical bodies. Existing statements and imports need no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Uses the preserved integral coefficient API or its map instances; identical names, signatures and bodies are publicly reexported. No adaptation. |

| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification | D8 | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | X7 | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Identical coefficient declarations and map instances remain available through original public reexports; no source adaptation. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | Identical coefficient declarations and map instances remain available through original public reexports; no source adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Identical coefficient declarations and map instances remain available through original public reexports; no source adaptation. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed | Identical coefficient declarations and map instances remain available through original public reexports; no source adaptation. |
| Sheaf.Paper.QcqsIntegralScalarExtensionCTF | unclaimed | Identical coefficient declarations and map instances remain available through original public reexports; no source adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | unclaimed | Conservative local-instance match; the encoding instance remains local and unchanged. No source adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Existing declarations and instances retain their names and bodies through public reexports; no code adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Existing declarations and instances retain their names and bodies through public reexports; no code adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Existing declarations and instances retain their names and bodies through public reexports; no code adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed | Existing declarations and instances retain their names and bodies through public reexports; no code adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Conservative textual match for EssentiallySmall Profinite; the identical local instance remains available through public reexports. No code adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Conservative textual match for EssentiallySmall Profinite; the identical local instance remains available through public reexports. No code adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Conservative textual match for EssentiallySmall Profinite; the identical local instance remains available through public reexports. No code adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Conservative textual match for EssentiallySmall Profinite; the identical local instance remains available through public reexports. No code adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Conservative textual match for EssentiallySmall Profinite; the identical local instance remains available through public reexports. No code adaptation. |

| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | T3 | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.DiagonalCompletedBaseChange | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.DiagonalCompletedRealization | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.DiagonalFamilyExtension | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.DiagonalFiniteReductions | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.DiagonalScalarBaseChange | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Conservative textual match for the anonymous EssentiallySmall Profinite instance; the encoding instance stays local with the same body. This module gains no instance or hypothesis; its existing imports and statements need no adaptation. |
| Sheaf.Paper.PadicConstantLocalModelTor | P3 | Relocated declarations retain their signatures and bodies through original public reexports; local instances stay local. Existing imports and statements need no adaptation. |

| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.DiagonalTracePresentationExistence | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.DiagonalTraceResultExistence | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.DiagonalTraceSingleFaithful | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralAdicHomCompleteness | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | U4 | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralSectionLocalModels | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.NoetherianScalarConstructibleHeart | E4 | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.QcqsLisseStratifiedIntegralLattices | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.SupportedThreeTermScalarRigidity | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |

| Sheaf.AlgebraicGeometry.ProperHeartIntegralHigherVanishing | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartScalarHigherVanishing | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralModelsEmbedded | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedCompletion | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedResidueComparison | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedStacksCriterion | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.LatticeQuotientSectionsRoos | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.LatticeQuotientTowerComplete | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |
| Sheaf.Paper.SupportedImageTorsionReductionsCd | unclaimed | Existing declarations retain their names and signatures through public reexports; local instances remain local. No source adaptation. |

## Status

open
