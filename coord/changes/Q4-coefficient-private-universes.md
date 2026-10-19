# Geometric module construction and transport private universes

## Reason

The coefficient-arrow theorem permits independent site object and morphism universes and
coefficients in universe w, assuming the sites essentially w-small. The existing proved
construction and transport helpers fixed all three universes to u. Generalize only those
private helpers so the proof can reuse their actual module construction and mate calculations.
All three public theorem signatures, their visibility, and their meanings stay unchanged.
Both edited support modules were unclaimed in the shared claim metadata when checked.
No definition used by a target statement changes; no target statement review is reopened.

## Old

In GeometricModuleConstruction, the private helper section had this context:

```lean
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
```

Its private imageModule sheaf proof used:

```lean
  refine ⟨N, (Presheaf.isSheaf_iff_isSheaf_comp K _
    (CategoryTheory.forget AddCommGrpCat.{u})).2 ?_⟩
```

The single-site private helper binders in GeometricModuleTransport were:

```lean
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
```

## New

The construction helper context is:

```lean
universe u uC vC uD vD uE vE
variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
```

Private product helpers also permit independent site sizes. Pure product/adjunction lemmas
omit the unnecessary EssentiallySmall hypotheses. Explicit ring-category universe parameters
keep coefficients in u. The sheaf proof uses the direction that does not require the larger
site itself to be u-small:

```lean
  refine ⟨N, (Presheaf.isSheaf_of_isSheaf_comp K _
    (CategoryTheory.forget AddCommGrpCat.{u})) ?_⟩
```

The single-site transport helper binders are:

```lean
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
```

The product-existence helper needs no EssentiallySmall hypothesis. Generic categorical mate
and product lemmas already have independent universes and are retained unchanged. There is no
change to geometric_module_construction, ringData_inducedModules, or geometric_module_transport
statements. The new Sites.Equivalence imports are proof-only.

## Users

The table includes every current direct importer listed by tools/downstream.py --direct,
every use of the three public names listed by the retained scan, both edited modules,
and this item. Transitive consumers receive the same public declarations and imports.
The prior attempt compiled its 12 unchanged direct consumer files through lcompile.py
against the two changed support modules (individual compiles 2.7 to 37.5 seconds).
The resumed scan found the additional importer CompletedPullbackAdjunction. Its first check
reached an unpublished dependency. A later check reaches compilation, but times out after
60 seconds both against the generalized support modules and against the unchanged server
baseline. The two consumer sources are byte-identical. This check remains incomplete;
the baseline failure does not establish a forced adaptation. Both support modules compiled
in this resumed check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.CategoryTheory.FlatRingedDiagramRestriction | J1 | No adaptation: public signatures and visibility unchanged |
| Sheaf.CategoryTheory.GeometricModuleConstruction | unclaimed | Private helper universe generalization; public signatures unchanged |
| Sheaf.CategoryTheory.GeometricModuleTransport | unclaimed | Private helper universe generalization; public signatures unchanged |
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | Y7 | No adaptation: public signatures and visibility unchanged |
| Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.CategoryTheory.RingedToposKFlatPullback | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.CategoryTheory.RingedToposSquareTransport | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.CategoryTheory.Sites.InverseImageFreeModule | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.Paper.CompletedPullbackAdjunction | unclaimed in current local claim snapshot | No adaptation: public signatures unchanged; unchanged baseline and changed-support checks both time out |
| Sheaf.Paper.FiniteSystemPullbackCoherence | Q8 | No adaptation: public signatures and visibility unchanged |
| Sheaf.Paper.RingedTopoiInverseImagePairing | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.Paper.RingedTopoiInverseImageTensorPairingIsIso | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.SixFunctors.RingedDerivedMonoidalComparisons | E2 | No adaptation: public signatures and visibility unchanged |
| Sheaf.TraceFormula.TotalSiteInjectiveCechResolution | unclaimed | No adaptation: public signatures and visibility unchanged |
| Sheaf.SecSmoothPurity.CochainCoefficientArrows | Q4 | Uses generalized private construction/transport helpers by proof-only import all |

## Status

landed 20261019T144018-L-2347992 2026-10-19 (merge of deliver/Q4/Sheaf.SecSmoothPurity.CochainCoefficientArrows)
