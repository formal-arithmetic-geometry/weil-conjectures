# Symmetric Proj chart proof elaboration

## Reason

The affine equivalence and final assembly otherwise expand the tensor pullbacks,
actual Proj twists, and relative-Proj chart colimit while comparing types. Compiler
diagnostics reported thousands of reductions of `colimit.cocone`, `Functor.obj`, and
scheme/sheaf projections; the final assembly reached the 60-second limit.

## Old

The item has the unchanged signatures and definitions
`AffineChartFormulas`, `AffineRestrictionFormulas`, and
`symmetric_proj_tautological_chart_gluing`, with the last proof `by sorry`.
There were no local transparency attributes for the constructions used by the proof.

```lean
def AffineRestrictionFormulas
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) : Prop :=
  ∀ (U V : S.affineOpens) (h : U ≤ V),
    ∃ t : (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).obj
          (Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1) ≅
            Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1,
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
          (D.chart V).hom ≫ t.hom =
        (Scheme.Modules.tensorPullbackSectionComp
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V)).inv.app D.line ≫
        (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj D.line)
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor_map_relProjι
            (homOfLE h)))).hom ≫ (D.chart U).hom ∧
      (∀ (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1),
        (Scheme.Modules.tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
            (Proj.unitToTwist ha) ≫ t.hom =
          ((Scheme.Modules.boundaryPullbackComparison
              ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
                (homOfLE h))).app (Scheme.Modules.unit _) ≪≫
            Scheme.Modules.pullbackObjUnitIso
              ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
                (homOfLE h))).hom ≫
          Proj.unitToTwist ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h |>.map_mem ha)) ∧
      (∀ (e : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (he : e ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1)
        (k : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V (k • 1)),
        Away.map ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h) e
            (Away.mk ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) he k a ha) =
          Away.mk ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
            (((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem he) k
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h a)
            (((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem ha))
```

## New

The section locally marks `Scheme.Modules.tensorPullback`, `tensorPullbackObj`,
`tensorPullbackSectionComp`, `tensorPullbackSectionAdjunction`,
`boundaryPullbackComparison`, `Scheme.GradedAlgebraData.relProj`, and `relProjι`
irreducible. The final assembly additionally protects the two affine predicates,
`Proj.twist`, `HasOpenCompatibility`, and `HasFreeCompatibility`.
Scoped `backward.isDefEq.respectTransparency` options limit proof elaboration to
the public APIs. The new descent and comparison modules use analogous local settings.
These attributes are local elaboration settings. In addition, the predicate is
refactored through `NormalizedAffineRestriction`, a structure holding exactly the
old isomorphism `t` and its two equations. A `Nonempty` wrapper supplies the same
existential assertion. The independent fraction equation is retained verbatim.
This changes packaging, with no added hypothesis or removed equation. The new module
is a public import because this predicate uses its structure.

```lean
def AffineRestrictionFormulas
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) : Prop :=
  ∀ (U V : S.affineOpens) (h : U ≤ V),
    Nonempty (NormalizedAffineRestriction E D U V h) ∧
    (∀ (e : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (he : e ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1)
        (k : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V (k • 1)),
        Away.map ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h) e
            (Away.mk ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) he k a ha) =
          Away.mk ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
            (((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem he) k
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h a)
            (((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem ha))
```

`NormalizedAffineRestriction.comparison`, `.chart_compatibility`, and
`.section_compatibility` unpack the old three witnesses; conversely those witnesses
construct the structure. No arbitrary data is chosen by a definition.
The original declaration signature and every target statement remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts | J2 | Equivalent predicate refactor, proof and local elaboration settings. |
| Sheaf.AlgebraicGeometry.SymmetricProjNormalizedDescent | J2, new | Local elaboration settings only. |
| Sheaf.AlgebraicGeometry.SymmetricProjOpenComparison | J2, new | Local elaboration settings only. |
| Sheaf.AlgebraicGeometry.SymmetricProjFreeComparison | J2, new | Local elaboration settings only. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | T2 | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.LineZeroGeometry | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No adaptation; no external use of the refactored predicate. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No adaptation; no external use of the refactored predicate. |

`tools/downstream.py --uses` reports that the predicate is named only in the item
itself (definition and theorem). The geometry parent consumes the unchanged theorem
and discards its last conjunction; every downstream statement therefore has the same
meaning. The full import-downstream list has 43 modules; none needs a forced adaptation.

## Status

landed 20261023T231626-L-3627249 2026-10-23 (merge of deliver/J2/Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts)
