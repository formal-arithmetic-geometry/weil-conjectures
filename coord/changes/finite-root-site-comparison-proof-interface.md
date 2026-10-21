# AlgebraicGeometry.Scheme.finiteRootSiteComparison

## Reason

Fill the theorem's sole proof hole by explicit scalar-extension Hom adjunctions
and the existing Cartier root comparison. Preflight requested this record because
it classifies private-import removal and proof-local attributes/options as an
interface change. No public definition, signature, global attribute or public
import is changed. No target meaning changes or second statement review is needed.

The original section-comparison proof import is retained as required by the
unit-route check. All adopted source files remain untouched. The added definitions
and lemmas are private. Local reducibility attributes and the local elaboration
option expose the existing constructions only while proving this theorem; the
original global irreducibility attributes remain verbatim.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.AlgebraicGeometry.CartierReductionData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

attribute [irreducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

theorem finiteRootSiteComparison (A : Type (u + 1)) [CommRing A] [Finite A] :
    FiniteRootSiteComparisonSpec A
```

The old theorem proof was `by sorry`.

## New

```lean


attribute [irreducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

theorem finiteRootSiteComparison (A : Type (u + 1)) [CommRing A] [Finite A] :
    FiniteRootSiteComparisonSpec A
```

The theorem now has a complete proof. New proof-local commands include:

```lean
attribute [local semireducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator
set_option backward.isDefEq.respectTransparency.types false
```

The remaining local attributes make restriction functors reducible and private
Hom equivalences irreducible during the private categorical calculations. None
is an exported declaration or a changed public definition. All twelve clauses of
`FiniteRootSiteComparisonSpec` and all its definitions are byte-identical.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteRootSiteComparison --uses
finiteRootSiteComparison finiteRootProModule finiteRootProTensor
finiteRootProGenerator FiniteRootSiteComparisonSpec` reports zero downstream
modules. Each name occurs only in the item itself. DAG parents remain attached;
zero current Lean importers is not used to authorize withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteRootSiteComparison | G7 | Proof completed; private helpers and local elaboration commands added; five unused private proof imports removed; all public interfaces retained. |

No other module is adapted, and no module is withdrawn.

## Status

landed 20261021T171801-L-3136903 2026-10-21 (merge of deliver/G7/Sheaf.AlgebraicGeometry.FiniteRootSiteComparison)
