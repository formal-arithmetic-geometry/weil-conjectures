# SignedLineScalarTensorTower proof elaboration

## Reason

Six existing theorem proofs now use proved private helpers. A closed
`CoefficientUniverses` section gives the tensor and basis helpers an independent
coefficient universe. Local reducibility attributes expose unit/restriction wrappers
and seal scalar-extension, tensor and recursive-comparison constructions behind their
projection lemmas. These commands reduce repeated unfolding during elaboration. The private basis-chart
constructor specializes a generic presheaf basis isomorphism, then lifts it directly
by the sheaf morphism constructor. The generic constructor is checked before the
slice-dependent helpers, avoiding repeated expansion of the slice functors. Generic
basis-transport helpers similarly avoid maximum-universe instantiations until their
public callers. The proof-only import
`import all Sheaf.Paper.ScalarExtensionDualLocalIso` exposes existing proved private
basis-coordinate and scalar-extension basis-isomorphism helpers. A private inverse-projection
lemma avoids unfolding the full imported isomorphism inside the transport argument.
Preflight conservatively classifies section and local attribute commands as an interface
change and requests this record. The unused-variable and style linters are disabled locally after the explicit interface comparison.
No existing public signature, definition body, public
import, visibility or global attribute changes. No target meaning changes.

## Old

```lean
set_option autoImplicit false

universe uC vC u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules
```

The four public definitions had their current bodies, and the seven theorem proofs were
`by sorry`. There was no private-helper section or local reducibility configuration.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option linter.unusedSectionVars false
section CoefficientUniverses
```

The new section is closed before the original public variables and all four public
definitions. Its generic helpers are private. Subsequent private helpers use the original
coefficient universe. Every added attribute is `[local reducible]`,
`[local semireducible]` or `[local irreducible]`; none is exported to importers.
`allowUnsafeReducibility` permits local attribute changes and does not add unsafe data or
change kernel checking. All private helpers have complete proofs or actual constructions;
none occurs in an existing public signature or definition body. Their public uses are
confined to theorem proofs. All eleven public signatures and all four definition bodies
were compared against the shared source and are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.SignedLineScalarTensorTower --direct` lists the five
direct importers below. There are 579 transitive importers in the current source.
The private helpers have no external users. Textual uses of the four definitions also
include the transitive consumer `SignedLineDerivedBaseChange`, listed below. All consumers
receive identical definitions, theorem signatures and public imports; no adaptation is
required and no consumer file is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SignedLineScalarTensorTower | X8 | Six proof bodies completed; original product hole retained; private helpers and local elaboration commands added. |
| Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.SignedLineScalarPullbackSquare | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.SignedTwistSiteTransport | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | unclaimed | Existing public interface unchanged; no adaptation. |

## Status

landed 20261024T191739-L-484068 2026-10-24 (merge of deliver/X8/Sheaf.Paper.SignedLineScalarTensorTower)
