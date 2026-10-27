# AlgebraicGeometry.Etale.ordinaryFiniteRootGenerator

## Reason

Use the scalar-extension adjunction transpose of the sheafification unit.
The previous formula composes the forgotten scalar-extension unit with the
forgotten sheafification unit. These are definitionally equal: for arbitrary
rings R and S, modules M and P, scalar map r and linear map s, the generic Lean
regression proves by rfl that the old forgotten composite equals
(ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars r s).hom.toAddMonoidHom.
The direct HomEquiv.toRestrictScalars component keeps the scalar-extension
construction abstract before specialization to roots of unity. Every datum remains explicitly constructed, with no choice of
an existence witness. Naturality is the private, proved general adjunction
naturality lemma. Local transparency settings protect scalar extension and the concrete
HasDerivedCategory.ofIsGrothendieckAbelian localization construction during
elaboration. The ordinaryFiniteClass and integral-generator data stay the same after replacing
the compatibility forget abbreviation by moduleAbelianForget. The public signatures and all coefficient
hypotheses stay unchanged. There are no new holes, modules or mathematical nodes. The same construction node also records the generic implementation helper described below.

## Old

```lean
def ordinaryFiniteRootGenerator (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf N).obj.obj W →+
      ((RawModuleScalarComparison.forget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA)).obj.obj W :=
  ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      ((toSheafify T.smallEtaleTopology
        (Scheme.finiteEtaleMuModulePresheaf T N ⋙
          ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA))).app W)).hom.comp
    (((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).map
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Scheme.finiteEtaleTwistScalar N A hA)).unit.app
        (Scheme.finiteEtaleMuModuleObj T N W))).hom)
```

## New

```lean
def ordinaryFiniteRootGenerator (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf N).obj.obj W →+
      ((moduleAbelianForget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA)).obj.obj W :=
  let M := Scheme.finiteEtaleMuModuleObj T N W
  let P := (Scheme.finiteEtaleTateLine T N A hA).obj.obj W
  let σ : (ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA)).obj M ⟶ P :=
    (toSheafify T.smallEtaleTopology (Scheme.finiteEtaleMuModulePresheaf T N ⋙
      ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA))).app W
  (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{0, u + 1, u + 1}
    (Scheme.finiteEtaleTwistScalar N A hA) σ).hom.toAddMonoidHom
```

The final performance repair also adds the data constructor
ordinaryFiniteClassCore with abstract category, derived-category and Ext
instances. Its body is `(Ext.mk₀ e).comp ((Ext.homEquiv.symm c).mapExactFunctor G)
(zero_add n)`. The old ordinaryFiniteClass body inlines that expression at the
concrete etale sheaf categories. The new body is
`ordinaryFiniteClassCore (moduleAbelianForget A T)
(ordinaryFiniteIntegralGenerator A T) F n c`, definitionally the same expression
after unfolding the helper. Existing public signatures, irreducibility and
class data are preserved. No caller needs an adaptation. Profiling the current
file gave 49.7 seconds and 41.7 seconds cumulative kernel checking before this
repair; the generic-core version gave 26.4 seconds and 22.9 seconds cumulative
kernel checking. The compiler limit and linter settings are unchanged. The
helper is implemented in the same module, not a split-off proof or new hole.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FramedForgetSupport | unclaimed | divisorForgetSupport evaluates ordinaryFiniteClass on its supported divisor class. The integral generator, scalar-forgetting functor and derived-class formula retain their data, so no source adaptation is needed. |
| Sheaf.Paper.FramedScalarMaps | unclaimed | Its divisor splice pushes the Kummer extension along ordinaryFiniteRootMap. The root map retains exactly the same section maps, so the scalar extension class is unchanged and no source adaptation is needed. |
| Sheaf.Paper.FramedTransport | unclaimed | divisorOrdinaryKummer applies Sheaf.H.map to ordinaryFiniteRootMap and the Kummer boundary in degree two. The root map's section maps are unchanged, so the divisor class and transport statements need no source adaptation. |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | unclaimed | etaleClass and the two-site comparison equations use ordinaryFiniteRootMap. Its section maps remain definitionally the same; the coefficient line and underlying forget functor retain their data. No statement or source adaptation is needed. |
| Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance | unclaimed | relativeKummerClass applies relativeKummerMapOnCohomology to ordinaryFiniteRootMap before the ordinary Kummer boundary. Its root map retains exactly the same section maps, so this class, its constants and the strict-local invariance statement keep their meaning. No source adaptation is needed. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | unclaimed | The simultaneous supported-root comparison states IsIso of ordinaryFiniteRootMap for the residue coefficient ring. Its section map and naturality are definitionally the original forgotten-unit construction, so the isomorphism assertion and all hypotheses keep their meaning; no source adaptation is needed. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | quarantined, currently unclaimed; H9 at return | Uses ordinaryFiniteRootMap in the finite-root isomorphism and supported Kummer boundary equations. Its section maps are definitionally unchanged. The archive is preserved verbatim, including its scalar-comparison import, which the item now keeps as a compatibility reexport. No H9 source adaptation or restoration is delivered. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | FiniteRoots.toLine composes comparisonUpperStar applied to ordinaryFiniteRootMap with forgetComparisonIso. The root map retains the same section maps definitionally, so the finite-root normalization and all signatures are unchanged; no source adaptation is needed. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Uses ordinaryFiniteRootMap as the explicit Kummer map and proves its section formula by rfl. The adjunction-transpose construction is definitionally the same map. Its other forget occurrence is Scheme.Etale.forget followed by Over.forget; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Defines the same section map; its naturality proof uses the generic adjunction equation. |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.AlgebraicGeometry.CartierProKummerDerivedUnit | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.AlgebraicGeometry.CartierReductionData | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.AlgebraicGeometry.CartierReductionModulus | unclaimed | Uses ordinaryFiniteRootMap and the historical forget abbreviation; the root map and scalar-forgetting functor keep the same data, so no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClassDefs | unclaimed | Uses ordinaryFiniteIntegralGenerator in the derived Cartier class formula; that generator's body and the scalar-forgetting functor are unchanged, so no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedChernNormalization | unclaimed | Uses and unfolds ordinaryFiniteClass in the supported Chern normalization; its body is preserved with the definitionally equal scalar-forgetting functor, so no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.AlgebraicGeometry.SpP1RationalPointChern | unclaimed | Uses ordinaryFiniteP1KummerClass in the rational-point Chern normalization proof; that definition and its root map keep the same data, so no adaptation is needed. |
| Sheaf.AlgebraicGeometry.SupportedKummerChernRealization | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | quarantined, unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.Paper.KummerAdditivity | quarantined, unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Uses ordinaryFiniteRootMap, whose section maps and meaning are definitionally unchanged. |

| Sheaf.Paper.FiniteReductionRootCharts | quarantined, unclaimed | Uses ordinaryFiniteRootMap to define the normalized root-line section. The same section map is retained definitionally; archive preserved without source adaptation. |
| Sheaf.Paper.PurityDivisorClass | quarantined, unclaimed | Uses ordinaryFiniteClass in the divisor normalization. Its data are preserved; archive preserved without source adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | quarantined, unclaimed | Uses ordinaryFiniteRootGenerator and its naturality equation in the explicit Tate scalar map. The generator is definitionally the original forgotten-unit composite; all section maps and equations are unchanged. Archive preserved; no source adaptation. |

The direct name scan for ordinaryFiniteRootGenerator finds only its own module;
the table additionally includes every ordinaryFiniteRootMap consumer and the
ordinaryFiniteP1KummerClass consumer found by the refreshed server preflight.
The subsequent preflight additionally identified CartierReductionModulus,
GeoCartierCycleClassDefs and OrdinarySupportedChernNormalization. Their rows
record the unchanged root map, integral generator and derived-class formula.
All three are unclaimed and require no source adaptation. Quarantine archives
are preserved. The equality check is universal before specialization, so zero
rings, N = 0, N = 1 and empty schemes are covered. Any target using the
construction is subject to definition review; the new formula is definitionally
the same map.

The 2026-10-22 audit additionally reads the three quarantined consumer sources
listed above. Their root maps, section equations and divisor normalization keep
the same data; no archive or source declaration is changed.

The return at head 5b0e73df3 identified DiagonalCoefficientDiagrams and
PurityRankOneLocalCalculation as further root-map consumers. Their individual
rows above record the actual comparison composite and explicit Kummer section
formula. Both are unclaimed. The root-generator data remain definitionally
unchanged, including the section formula proved by rfl in the latter consumer.

## Status

landed 20261024T015347-L-2367834 2026-10-24 (merge of deliver/P2/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
