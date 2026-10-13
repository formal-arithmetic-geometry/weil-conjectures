# etaleOpenSmallRestriction

## Reason

Prune unused proof imports and replace the broad public Etale complement import
with its Small dependency. The public restriction definition uses
Scheme.isContinuous_overMap from Small. No original declaration signature,
definition body, hypothesis or conclusion changes. This records the reduction
in transitively public exports, as required by the stage-3 preflight.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
```

The etaleOpenSmallRestriction signature and body are byte-identical; the existing
theorem signature is byte-identical. Only imports and the theorem proof change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen | unclaimed | Direct public importer, compiles unchanged against the sandbox overlay; its other public imports provide the Etale complement independently. No statement meaning changes. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology | H3 | Direct private importer, compiles unchanged against the sandbox overlay. No statement meaning changes. |

Ran tools/downstream.py with --uses etaleTensorSectionsSheaf_openIdentification
etaleOpenSmallRestriction: neither name is mentioned by any downstream module.
There are 141 transitive importers, but neither of the two direct importers needs
adaptation; the other public dependencies of EtaleCohomologyOverOpen already expose
the Etale complement. The target statements and the definitions they use retain
the same meaning. No adaptations are delivered.

## Status

landed 20261013T004026-L-2491763 2026-10-13 (merge of deliver/P3/Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification)
