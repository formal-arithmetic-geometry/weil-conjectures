## What changed

Proved `WeilConjectures.IntegralAmbient.integralAmbientOperationModels` in
`Sheaf.Paper.IntegralAmbientOperationModels`. Ordinary pullback is presented using
independent-universe inverse image and scalar extension; uniqueness of left
adjoints identifies it with the specified pullback. The existing ringed derived
pullback theorem and universal cochain counit transport provide the ambient
left-derived functor and its counit, invertible on good representatives.

A proved general completion-descent argument uses fully faithful whiskering
along good localization, and along its product for tensor. It constructs the
natural comparisons and proves their component and augmentation equations.
Functoriality of localization combines the quotient Roos unit with the prescribed
strict tower map. All original coordinates and the unresolved pullTowerModel plan
are preserved.

The ambient module imports the new proved
`Sheaf.CategoryTheory.RingedPullbackCochainPresentation` interface. That module
privately imports the independent ringed-pullback implementation and universal
cochain counit transport, and combines their conclusions. The ambient proof then
transports this cochain counit along the same left-adjoint isomorphism.
The existing node and the new interface node record this route.

The public operation interface shares explicitly constructed functors, comparisons
and their compatibility laws in one record. Its specifying theorem is fully proved
and determines the record by literal equality to `rawAmbientPackage`;
`ambientPackage_eq` proves that equality. The non-target theorem and
`tensorRepresentative` signatures use these exact projections to avoid repeated
kernel evaluation of the original cochain constructions. Their mathematical
content and hypotheses are retained, and semantic review is reopened through
`coord/changes/S7-integral-ambient-operation-interface.md` and
`coord/changes/S7-integral-ambient-tensor-representative-alias.md`.
No source-library module or Challenge declaration is modified. The public category
instances support the new carrier interface.

Repair C-835f8 identified that the original private proof import exposed broad
semilinear instances to `import all` consumers despite local attribute removals.
The first repair adapted `PointIntegralTensorChain`, but returned head d9fdf4b33d0
did not land because that consumer and `PointFibreDerivedTensorModels` had been
quarantined at 2026-10-26 10:20:36 UTC for a separate dependency failure.
This packet fixes the import boundary instead: the new proved interface keeps the
semilinear implementation private, and the ambient module imports only that
interface. No consumer adaptation or restoration is now needed or delivered.
Both archives, all declarations, Lean attachments and dependencies remain intact;
no deleted.txt or empty module is used.
The import-isolation change record is
`coord/changes/S7-point-integral-tensor-chain-instance-repair.md`.

The retained proof was compared with the current 722-line published module; its
original completed-coordinate and strict-tower proofs remain intact. The repair
changes the new proof-import path and counit assembly, not an existing public
signature relative to the returned delivery.
The current two delivered modules compile without errors or warnings in result
`d75d38e4faafa808101aecc0`: 9.7 seconds for the new interface and 48.6 seconds for
the ambient module. Result
`0d37ec7a9ea3c8d9897d37dd` then verifies an `import all` probe with
`Lean.Meta.getInstancePriority?`: neither semilinear instance is active (5.2 seconds).
It also compiles the unchanged archived `PointIntegralTensorChain` against the
repaired sibling ambient module (44.4 seconds, no errors or warnings). The tested
consumer is byte-identical to its current quarantine archive. These two temporary
test files are preserved only under scratchpad and are not part of the packet.

All added data is explicitly constructed or selected by a proved universal/unique
specification; no definition contains sorry. No module or proof was split for timing.

## Proved and sorry left

Closed one of two original holes:
`WeilConjectures.IntegralAmbient.integralAmbientOperationModels`.

One original hole remains:
`WeilConjectures.IntegralAmbient.pullTowerModel`, node
`lem-pur-integral-ambient-operation-models`. Its original complete docstring plan
and strict coefficient-comparison route remain unchanged.

Added zero holes and split off zero unproved statements. The new theorem
`SheafOfModules.ringedPullbackCochainPresentation` is fully proved and has zero holes.
All other added support properties and private helpers are proved. This is a proof
from the project's existing declared dependencies, some of which still contain
sorry; it does not claim that the full target import closure is axiom-free.

## No longer needed

No module is withdrawn. Relative to the returned head, the ambient module's direct
proof imports of `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` and
`Sheaf.CategoryTheory.CochainUniversalCounitTransport` are replaced by the new
proved cochain interface. Both remain private proof dependencies of that interface;
no global pruning of either is claimed. The attempted consumer adaptation is no
longer needed because the source import leak is repaired.

The final descent uses
the existing derived and localization APIs, so it removes these direct proof
edges from the earlier unimplemented realization plan:

- `lem-pc-kflat-resolution`
- `lem-pc-quasi-isomorphisms-multiplicative-system`
- `lem-pe-kflat-scalar-tower-realization`
- `lem-pur-derived-change-of-rings`
- `lem-pur-kflat-change-of-rings`
- `lem-weil-pbc-resolving-representative-whiskering`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-restriction-of-scalars-exact`
- `lem-weil-strict-roos-derivation`

The same ten obsolete maintainer tool-use entries are removed from the node,
without adding or reordering other approvals. These results can remain transitive
library dependencies; no global unreachability or module withdrawal is claimed.
The unfinished strict pullback comparison retains
`lem-pur-strict-coefficient-comparison-calculus` and its planned argument.

## Where the brief, the DAG or earlier work was wrong

The previous final-theorem route repeated K-flat resolution, fractions,
restriction-exactness and derived-limit constructions already encapsulated in
existing comparison and localization interfaces. Reusing those interfaces gives
the specified strict tower and augmentation formulas directly. The original Lean
presentation also repeatedly expanded large cochain object constructions during
kernel conversion; the proved equality of the shared operation record supplies an
explicit interface for the same data. No mathematical statement was found false,
and no unit route is bypassed.

## Forced adaptations

None in this packet. Reviewer C-835f8 explicitly permitted either the two-line
consumer adaptation or preventing the semilinear import from reaching `import all`
users. This repair implements the latter. The original baseline errors at
PointIntegralTensorChain lines 53:80 and 62:2 were reproduced in result
`f70d1ede5fc5871b54783a14`; that evidence motivated the boundary repair.
The quarantined source and its dependencies are preserved unchanged. Import-all
instance inspection and the successful unchanged-consumer compile in result
`0d37ec7a9ea3c8d9897d37dd` verify the alternative repair directly.

## New nodes

`lem-pur-ringed-pullback-cochain-presentation`, implemented by
`SheafOfModules.ringedPullbackCochainPresentation` in
`Sheaf.CategoryTheory.RingedPullbackCochainPresentation`, is a fully proved
combination of the existing independent-universe derived ringed pullback and
universal cochain counit transport theorems. It states right Kan universality and
invertibility on flat-term K-flat cochains using the actual module-sheaf categories.
Its source is Stacks Tag 06YY with the existing categorical transport refinement.
LeanSearch, LeanFinder, Mathlib grep, and the existing project declarations were
searched. This module is introduced for import isolation, not to split a slow proof
or postpone any mathematics. No unit route is changed.

Change records:
`coord/changes/S7-integral-ambient-operation-interface.md`,
`coord/changes/S7-integral-ambient-tensor-representative-alias.md`, and
`coord/changes/S7-point-integral-tensor-chain-instance-repair.md`.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
