## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange`
and proved `AlgebraicGeometry.Etale.genericDirectImageExchange` with its original statement,
including both invertibility and the specified canonical four-arrow composition equality.
The proof follows the unit route: ordinary generic projection, field extension, then mate pasting.
All new helpers are private and proved.

The generic limit uses the already proved source `Scheme.isLimitFunctionFieldCone`, transported
to the chosen fraction field; connected-limit preservation in over categories gives its base
change to Y. The two abelian bounded-below exchanges are transported to the actual unbounded
constant-module mates using the stated comparison lemmas. The field-extension square is moved
from iterated pullbacks to the prescribed corners by explicit canonical pullback isomorphisms.
An explicit cone isomorphism avoids expensive elaboration of the generic limit cone.

Repaired the returned packet against the current comparison shim. The earlier delivery
59bc978e2a was reviewed successfully but failed to land because D2's 3748be6966 had
already changed `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`.
The retained packet would have removed its private evaluation-acyclicity helper,
which `Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic` still needs via `import all`. The sandbox comparison module now matches
the current repository byte for byte, including its `import all`, private alias, and
proved private wrapper. Its three ancillary DAG node copies also match the current
repository, preserving D2's canonical attachments and the wrapper's Sheaf attachment.
Only the restored item and its proof-route node change in the final delivery.

The old proposed comparison change record is removed from this packet: the current
repository already provides the canonical re-export and no interface repair remains
to land. No source-library file, consumer, definition, or public signature changes.
`deliver3.py` rebuilds the delivery commit on the freshly fetched `sheaf-dag` tip.

Validation: `lcompile.py --all` compiled the repaired sandbox cleanly on the server.
The item took 13.9 seconds; both modules have zero local holes. Delivery preflight
is rerun against the freshly fetched delivery base.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Etale.genericDirectImageExchange`
(node `lem-sf-etale-generic-direct-image-exchange`).

One of one original holes closed; zero holes added; zero holes remaining in the delivered
modules; zero split-off statements. This proves the item from existing stated dependencies;
it does not claim to close the remaining holes inside imported dependencies.

## No longer needed

Removed the item's private imports:

- `WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`: use the already proved
  generic-point specialization in `WeilConjectures.AlgebraicGeometry.FunctionFieldLimit`.
  The local-ring limit node is retained as the mathematical input specialized by that theorem.
- `WeilConjectures.AlgebraicGeometry.LimitFibreProducts`: use pullback and forgetful functors'
  preservation of connected limits.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: no properness argument is required.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: the used API is supplied by Coherence.

Removed the dependency and top-level tool approval `lem-weil-pbc-limit-fibre-products` from the
item's node. Its geometry is replaced by the categorical limit argument above. The remaining
smoothness and qcqs geometric nodes are realized through the corresponding Mathlib instances.
No module is withdrawn; other consumers can still need every removed import. The current
repository already consolidates the duplicate Sheaf comparison implementation through its canonical compatibility re-export; this packet
preserves that shim and its private API verbatim. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The absent item was quarantined because its declared proof imports combined duplicate globally
named module/abelian comparisons. Its absence was not withdrawal. Simply dropping the comparison
import would not implement the coefficient transport in the proof. The current canonical
source re-export repairs the collision while preserving consumers and the source boundary.
The returned packet predated D2's compatibility wrapper; preserving that wrapper resolves
the reported landing conflict without undoing the intervening work.

The DAG's geometric limit plan is mathematically sound; a proved source specialization and
Mathlib connected-limit preservation give a shorter Lean implementation of its first two steps.
No mathematical statement, hypothesis, target meaning, or canonical exchange definition changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
