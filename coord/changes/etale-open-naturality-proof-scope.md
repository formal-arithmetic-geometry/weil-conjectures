# etaleOpenTensorSectionsComponent_naturality

## Reason

The stage-3 interface scanner flags added scope commands. The proof opens
`Scheme.Modules`, sets backward elaboration transparency options, and locally
marks the expensive tensor pullback definitions irreducible. These commands
control name resolution and elaboration in this file. The attribute is local;
all existing public signatures, visibility, public imports, and the public
component definition body stay identical. No statement or definition of a
mathematical object changes, and no target requires a meaning review.

## Old

```lean
universe u
open CategoryTheory
namespace AlgebraicGeometry
```

No elaboration options, additional open command, or local irreducibility
attribute appeared before the component-isomorphism declaration.

## New

```lean
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj
```

Five proved private helpers and the complete public theorem proof are added.
The only new imports are private proof imports. No existing signature or
visibility changes and no helper occurs in any public signature or definition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality | M3 | Proof elaboration commands and private helpers; existing public interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification | unclaimed | Only external textual user of either public declaration; compiles unchanged against the delivered module. |

`tools/downstream.py` with both public names reports these two textual users,
including the item itself; 142 modules are downstream by imports. The direct
importer still constructs the same componentwise presheaf isomorphism using the
same theorem type. There are no adapted modules and no forced adaptations.

## Status

landed 20261013T024039-L-3336170 2026-10-13 (merge of deliver/M3/Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality)
