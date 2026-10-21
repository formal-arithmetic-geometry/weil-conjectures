# Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest

## Reason

All four original theorem holes are filled. Remove redundant imports after proving
these statements by explicit model-site Hom equivalences and sectionwise tensor
lifting. The retained public comparison import already publicly imports the inverse
image module; its tensor interface supplies all types used here. No existing public
signature, declaration visibility, docstring or definition body changes.

The private construction uses `backward.isDefEq.respectTransparency.types false`
for elaboration of the site transports. This affects elaboration in this file only.
The local unused-variable linter suppression surrounds the composition proofs:
the fixed public statement includes ring compatibility `hc`, while the stronger
module normalization hypothesis `hd` suffices in this proof. The proved private
adjunction is irreducible to prevent costly expansion during subsequent proofs.
All private declarations are fully proved or concrete constructions. There is no
new public declaration and no added hole. The final file compiles cleanly with
standard heartbeat and time limits in 28.4 seconds.

## Old

The original import and option commands were:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.GeometricModuleTransport
```

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
```

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The two composition declarations additionally use declaration-scoped
`set_option linter.unusedVariables false in`. The helper adjunction uses
`@[irreducible] private noncomputable def testAdj`. These commands introduce no
public interface and change no target statement or definition meaning.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest --count`
reports zero current Lean consumers. No consumer adaptation is needed. DAG parents
are preserved; this record does not withdraw the item or any dependency module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest | P4, assigned | Fill four proofs; remove redundant imports; add proved private helpers and local elaboration options. |

No module held by another group is adapted. All adopted source-library modules
and all target signatures remain unchanged.

## Status

landed 20261021T193706-L-1266288 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest)
