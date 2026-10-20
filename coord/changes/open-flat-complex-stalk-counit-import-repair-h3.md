# AlgebraicGeometry.openFlatComplex_stalk_counit

## Reason

Restore the quarantined module for the rework assignment recorded in coord/rework.tsv.
The archived source fails to import after upstream sync 5f7b33eac because
SingleComplexBaseChangeStalkCondition uses the retained Sheaf base-derived tensor model,
whereas two proof imports load its upstream twin. The reproduced compiler diagnostic is:

```
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel failed,
environment already contains 'ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst'
from Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The archived module already had zero holes. This is an import/proof repair, with no
new proof-hole closure claimed. Its public imports, existing declarations and theorem
signature remain identical. No definition, instance, statement or source-library file changes.

## Old

The proof-only imports were:

```lean
import all WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryRingComparison
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
```

The ordinary comparison used ModuleCat.exists_extensionComplexIso from the first
module. The scalar counit used ModuleCat.scalarExtensionCounit_isIso_of_kFlat from
the second, after converting the categorical K-flat predicate to acyclic tensor flatness.

## New

The replacement proof-only imports are:

```lean
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
```

A fully proved private extensionComplexIso identifies the composite scalar functors
by Mathlib's conjugateIsoEquiv, using the commuting square of scalar restriction
right adjoints, and lifts this isomorphism termwise. The existing scalar-extension
quasi-isomorphism helper supplies PreservesKFlatQuasiIso, so the generic
isLeftDerivedFunctor_iff_isIso_app_of_kFlat applies to P directly. The final
counit-cancellation argument and all public signatures are preserved.

## Users

The live downstream query with --allow-missing lists no users because the item and
its parent are quarantined. The quarantine source and DAG searches identify the
following real consumers; their attachments and dependencies are retained.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit | H3 | restored with proof-only repair; same public interface |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology | unclaimed | direct theorem call unchanged; original archive compiled against the repaired module |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | unclaimed | transitive consumer through LocalizationHomology; no signature or meaning change |

No consumer adaptation is required or delivered. Scratch compiler checks are outside
the delivered lean tree. The proof of the item and both private helpers have exactly
propext, Classical.choice and Quot.sound as axioms.

## Status

landed 20261020T150642-L-2552112 2026-10-20 (merge of deliver/H3/Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit)
