# CategoryTheory.quasiIso_homComplex_mapOfUniverses

## Reason

The assigned derived internal Hom uses module and coefficient elements in
`max c v r`, whereas the existing invariance and sectionwise criteria use
`max c v`. Add universe-general companions of these three source statements and their
complete comparison and restriction proof chain in twelve new modules. Keep all
original specialized declarations and proofs unchanged. The source statements
are independent of these size coincidences. All twelve companions are proved.

## Old

The following signatures use `{C : Type u} [Category.{v} C]`, ring/module
universe `max u v`, and otherwise the hypotheses and conclusions of their
source nodes. Their source files are unchanged by this delivery:

```lean
theorem quasiIso_homComplex_map
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] :
    QuasiIso (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)
```

```lean
theorem quasiIso_of_sections
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}}
    {K L : CochainComplex (SheafOfModules.{max u v} R) ℤ} (f : K ⟶ L)
    (h : ∀ U : C, QuasiIso (((SheafOfModules.forget R ⋙
      PresheafOfModules.evaluation R.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) : QuasiIso f
```

```lean
theorem homComplex_sections_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] (U : C) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    QuasiIso (((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s))
```

## New

```lean
theorem quasiIso_homComplex_mapOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J CommRingCat.{max u v r}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] :
    QuasiIso (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)
```

```lean
theorem quasiIso_of_sectionsOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J RingCat.{max u v r}}
    {K L : CochainComplex (SheafOfModules.{max u v r} R) ℤ} (f : K ⟶ L)
    (h : ∀ U : C, QuasiIso (((SheafOfModules.forget R ⋙
      PresheafOfModules.evaluation R.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) : QuasiIso f
```

```lean
theorem homComplex_sections_quasiIsoOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J CommRingCat.{max u v r}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] (U : C) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
    QuasiIso (((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s))
```

All three are proved, as are the nine supporting universe companions listed
below. Each companion has a NEW node; the original specialized nodes retain
their Lean records unchanged. Only the assigned node changes its proof route,
proof dependencies and proof origin. No existing natural-language statement,
declaration, public import, instance or definition changes. No target statement
requires reinterpretation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses | new in E2 delivery | Proved from the two generalized sectionwise criteria, imported privately. |
| Sheaf.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses | new in E2 delivery | Proved sectionwise invariance from the completed universe-general comparison chain. |
| Sheaf.Algebra.Homology.QuasiIsoOfSectionsOfUniverses | new in E2 delivery | Proved generalized detection criterion; existing version unchanged. |
| Sheaf.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses | new in E2 delivery | Derived comparison naturality; proved. |
| Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses | new in E2 delivery | Homotopy comparison naturality; proved. |
| Sheaf.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses | new in E2 delivery | Cycles and homology comparisons; proved. |
| Sheaf.Algebra.Homology.HomComplexSectionsCochainsOfUniverses | new in E2 delivery | Product-based additive cochain equivalences; proved. |
| Sheaf.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses | new in E2 delivery | Compatibility with the Hom differential; proved. |
| Sheaf.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses | new in E2 delivery | Preservation of K-injectivity by restriction; proved. |
| Sheaf.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses | new in E2 delivery | Exact restriction preserves quasi-isomorphisms; proved. |
| Sheaf.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses | new in E2 delivery | Exact left adjunction and additive restriction; proved. |
| Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses | new in E2 delivery | Concrete sheafified direct-sum left adjoint; proved. |
| Sheaf.Algebra.Homology.QuasiIsoHomComplexMap | unclaimed at inspection | Unchanged declaration and proof; the generalized theorem is additional. |
| Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses | E2 | Uses generalized theorem in all three completed proofs. |
| Sheaf.Algebra.Homology.DerivedCoinductionAdjunction | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedInternalHom | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.HomComplexHypercohomology | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.HomComplexResolutionShiftComparison | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.HomologyEvaluationLocalIso | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.HomologyEvaluationRoofComparison | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.KFlatRHomCurrying | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.RingedInternalHomExactRestriction | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedSingleHomEvaluation | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.AlgebraicGeometry.LocalFiniteFreeHomologyNatural | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Paper.CoefficientHomRepresentativeEvaluation | unclaimed | Unchanged old API and public imports; no adaptation required. |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | unclaimed | Unchanged old API and public imports; no adaptation required. |

The existing API is unchanged; these consumers keep their signatures and proofs.
The assigned module imports the new invariance theorem privately. The generalized
invariance theorem imports its two generalized dependencies privately. No module
held by another group is adapted.

## Status

landed 20261019T002530-L-2148805 2026-10-19 (merge of deliver/E2/Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses)
