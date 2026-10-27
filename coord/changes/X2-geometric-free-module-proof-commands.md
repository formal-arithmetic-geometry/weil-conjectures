# CategoryTheory.SheafFreeModule.geometricFreeModule_hom_chain

## Reason

Preflight requests a change record for the proof's additional section, open and
local attribute commands. They support private proved helpers at the independent
site universes of the existing theorem. No public declaration signature, definition
body, public import, or target statement changes. All new declarations are private;
all added instance registrations and irreducibility attributes are local.

The proof-only construction and transport imports use `import all` to access their
already proved APIs. This records the command-level change for the independent
reader; it introduces no alternative mathematical definition for an importer.

## Old

```lean
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.GeometricModuleTransport

open CategoryTheory CategoryTheory.Limits
```

The existing theorem has the same signature and a `sorry` proof. The definitions
`inverseFreeRestriction` and `directModuleTranspose` are retained verbatim.

## New

```lean
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import all Sheaf.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
```

The proof's private helper section additionally registers these local instances:

```lean
attribute [local instance] SheafOfModules.sheafHasBinaryProduct
attribute [local instance] composeRings composeRingSets composeGroupSets
  composeLiftRingSets composeLiftGroupSets composeLift
```

`ComposeInstances` encloses private proved sheaf-composition instances and closes
before the main proof. Local irreducibility controls keep the existing free object
and the existing Hom-restriction implementation from unfolding during elaboration:

```lean
attribute [local irreducible] free
attribute [local irreducible] mateIsoEquiv restrictHomEquiv
```

The three existing public declarations have unchanged signatures, and both public
definition bodies are unchanged. The theorem now has a complete proof, including
all operation graphs and naturality equations. No global instance, public helper,
notation, or change to an existing definition is introduced. No target review is
reopened.

## Users

Computed with `tools/downstream.py` and its `--uses geometricFreeModule_hom_chain`
search. The only direct importer and only external textual user of the theorem is
`InverseImageFreeModule`: its `transportedFreeProperty` extracts the same `hBij`
conjunct. Its further use of `inverseFreeRestriction` sees the identical definition.
The remaining rows are all 15 transitive importers reported by that command.
Claims were checked in the current shared metadata; no consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence | X2 | Complete proof and private local proof commands; public interface unchanged |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.Algebra.Homology.RingedSitePointFinitePresentationRetract | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.Algebra.Homology.RingedSitePointUniversalTensor | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineSchemeDeformationComparison | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexTensorInheritance | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.MarkedSchemeLifts | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SchemeCoefficientExtensionProblems | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SchemeCotangentOpenRestriction | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SchemeLiftClassificationData | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SchemeSquareZeroLiftTorsor | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ZariskiSquareZeroExtensions | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.CategoryTheory.Sites.InverseImageDifferentials | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.CategoryTheory.Sites.InverseImageFreeModule | unclaimed | Uses unchanged theorem and definition; no adaptation |
| Sheaf.Topology.SheafCotangentComparison | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.Topology.SquareZeroSheafAlgebra | unclaimed | Transitive importer; public interface unchanged; no adaptation |
| Sheaf.Topology.ZariskiSheafAlgebraExtensionExt | unclaimed | Transitive importer; public interface unchanged; no adaptation |

## Status

landed 20261024T022003-L-2887306 2026-10-24 (merge of deliver/X2/Sheaf.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence)
