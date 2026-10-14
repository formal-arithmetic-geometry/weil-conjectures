## What changed

Retained the restored `Sheaf.Paper.ModuleCupDerivedClassComparison` from the complete source in
`coord/repair-notes/Sheaf.Paper.ModuleCupDerivedClassComparison.json`. The assigned module and
its node had been removed after a red build. The restored public declarations and their
signatures are unchanged from that delivery: `cupDerivedSections`, `CupDerivedClassComparison`,
and `exists_cupDerivedClassComparison`.

The comparison is constructed from actual injective resolutions, extension-by-zero cycles and
homology isomorphisms. The proof transports the comparison through the augmented resolution
map using naturality, then evaluates the homology equation on the explicitly lifted cycle.
It introduces no unspecified witness or unproved helper. This repair also explicitly names
its local coefficient-ring instance `cupDerivedClassCommRing`, so restoring the module does
not introduce another anonymous generated instance name shared with the cup modules.
The instance has the same type, body, local scope and `instance_reducible` attribute.
The earlier restoration cleaned one redundant tactic block and removed an unused import.
Its node records the actual proof route and executed searches.

Rechecked the returned failures against the current published dependencies.
The reported duplicate-instance failure is already repaired in the current dependency:
`ModuleCupKInjectiveTarget` now names its local symmetric instance `moduleCupTargetSymmetric`.
The assigned comparison compiles against these published dependencies; no dependency source
or unrelated module is included in this delivery. The existing
`ModuleCupDerivedHomologyTensor` supplies `cupLocalizedCycleClass`, so its original 28-line
helper replacement is deliberately not replayed over the current, larger proved module.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.exists_cupDerivedClassComparison` has a complete Lean proof.
All its private helper proofs are complete. The scratch axiom probe of
`exists_cupDerivedClassComparison`, `cupDerivedSections`, `CupDerivedClassComparison`, and
`cupLocalizedCycleClass` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
For transparency, the imported `exists_cupDerivedHomologyTensor` still depends on `sorryAx`
through existing library dependencies; this delivery does not change or use that theorem.
It uses only the proved localized-cycle definition from that module. No `sorry` is left in
the delivered module and no new hole is added. The present base has no source file for this item, so this is a restoration
and repair, with zero textual baseline holes closed, rather than a claim of new net proof
progress. The previous failed delivery already contained this proof.

Edge cases: degree zero is covered by the embedding's cycles and homology isomorphisms; no
positive-degree assumption is used. Zero sheaves and zero cycles satisfy the same linear
identities. The construction uses only the stated derived-category instance and the library's
enough-injectives theorem; it imposes no flatness, properness or acyclicity beyond the computing
resolution data in the unchanged statement.

## No longer needed

Removed the redundant proof import
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` from the restored source;
the required extension API is already available through the necessary public imports.

The old planned dependency `lem-sc-module-cup-resolution-invariance` and module
`Sheaf.Paper.ModuleCupResolutionInvariance` are not needed for this comparison. Its statement
concerns products, whereas the class comparison follows directly from injective-resolution
naturality. In particular it must not be imported here: its evaluation branch uses this class
comparison. The broad `lem-sp-kinjective-computes` and module
`Sheaf.CategoryTheory.KInjectiveComputes` are also unnecessary: the existing Mathlib
`CochainComplex.isKInjective_of_injective` and right-derived unit instance supply the exact
special case. These are local pruning claims, not claims that these modules are unreachable
from every project target. The unit's `realized` lists are empty, so no designated unit step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

This is a repair handoff, although the dispatched brief describes a present module with
`sorry`. The module is absent and its source must be recovered from the repair note. The old
failure was an import-time collision, rather than a mathematical proof gap. Current named
instances eliminate that collision. Both reported failing modules are addressed without
editing the already restored `ModuleCupDerivedHomologyTensor`: it is imported unchanged and
the comparison's axiom probe loads the combined environment.

The removed node cited product resolution invariance for a single-class comparison and used
itself as its blueprint ancestor. The restored node records the direct naturality argument,
the actual definition dependencies, the theorem-of-the-cube ancestor, and searches run in
the earlier restoration session. LeanFinder found general sheaf cohomology and Ext infrastructure; Loogle did
not recognize the queried identifier; LeanSearch returned HTTP 500; Mathlib source grep and
reading found the right-derived homology and naturality lemmas used here. The Stacks checkout
is not present on this machine, so Tags 01DZ and 0FKU were read on the Stacks website.

Return-point audit in this repair session:

1. The comparison's failed axiom probe was caused by the duplicate anonymous symmetric
   instance. The published `ModuleCupKInjectiveTarget` now uses the explicit name
   `moduleCupTargetSymmetric`. The restored comparison compiles cleanly in 29.6 seconds.
2. The comparison module's attributed importer failure is repaired by retaining its complete
   original interface. No current source module imports the removed comparison, and this
   delivery changes none of its former public signatures. There is no forced consumer edit.
3. The former delivery replaced `ModuleCupDerivedHomologyTensor` with a small helper-only
   module. This delivery omits that replacement: the current complete source, including
   `CupDerivedHomologyTensor` and `exists_cupDerivedHomologyTensor`, is preserved. An exact
   scratch copy of that source compiles unchanged in 10.6 seconds against the published build.
4. The homology module's failed batch probe shared the same conflicting import environment.
   The current comparison imports both the compatibility/K-injective branch and the complete
   homology module successfully. The dry run runs the declaration axiom/sorry probe and passes
   preflight. No dependency adaptation is delivered or needed.

The old second-reading section has been removed; the independent reader must review this
repair anew. The assigned module receives the explicit local instance name; no source change
to the already repaired dependencies is replayed. No additional holes are claimed closed by
this repair audit.

Additional process issue, outside the returned dependency pair: a scratch stress check with
an extra direct import of `GlobalTensorPullbackMonoidalNormalization` before the comparison's
imports failed while importing `ModuleCupNaiveDerivedCompatibility`, because both modules
export the same generated anonymous local CommRing instance name. The error begins
`import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility failed, environment already contains`
and attributes the earlier declaration to `GlobalTensorPullbackMonoidalNormalization`.
The delivery does not add that direct import, and its actual import graph compiles. This
remaining cross-module naming issue is reported for the maintainer; neither unrelated module
is adapted here because no change of this delivery forces an adaptation.

## New nodes

`lem-sc-module-cup-derived-class-comparison` is restored as the statement node of the removed
comparison module. It records the family of linear isomorphisms and the cycle representative
formula, with a three-step proof matching the local injective comparison, naturality transport,
and cycle lift/evaluation. It has no unproved Lean declaration. No new intermediate theorem
module or mathematical interface change is delivered. The named local instance replaces its
anonymous generated name, as recorded in the change record. The restoration record is
`coord/changes/ModuleCupDerivedClassComparisonRestore.md`.

## Second reading by D2

1. Interface preservation: the repository module is absent. Extracted its complete prior
   source from the repair note's diff and compared it with the sandbox. The only differences
   are removal of the ExtendMap proof import, naming the local CommRing instance, and removal
   of one redundant `by exact` block. All public signatures and definition bodies are byte
   for byte unchanged. The restoration and local instance rename have a change record. Pass.
2. Proof validity: independently compiled the delivered file (25.7 seconds) and a scratch
   copy with `#print axioms` (23.3 seconds). The existence theorem, abbreviation, and structure
   each report only propext, Classical.choice, and Quot.sound. Scanned the full file for
   sorry, axiom, unsafe, opaque, implemented_by, extern, and skipKernelTC: none occur. The
   private definitions construct actual resolutions and composites of isomorphisms; no data
   comes from an unproved existence theorem. Pass.
3. Split statements: none are added or left open. Read the construction and cycle transport
   from top to bottom. Degree zero uses the same extension cycles and homology isomorphisms;
   zero cycles map to zero under the linear maps. No positivity, flatness, or properness
   hypothesis was introduced. Searched the cup modules for isoRightDerivedObj,
   extendCyclesIso, homologyFunctorFactors, and cupDerivedClassComparison: supporting class
   and naturality infrastructure exists, but no replacement for this full comparison. Pass.
4. Route and pruning: the proof uses Mathlib's injective-resolution comparison and homology
   naturality directly. All three public imports provide identifiers in the structure's
   signature, so none is proof-only. The removed ExtendMap import is redundant. Both old
   proof_deps are accounted for under No longer needed. Checked sk-prop-av-cube.json:
   realized.statement is empty and realized.steps is [[]], so no designated step is
   bypassed. No shorter existing route was found. Pass.
5. Node consistency: read every proof dependency's Lean or Mathlib record and checked the
   restored node's three proof steps against injectiveClassIso, the transport lemmas, and
   the cycle lift/evaluation. proof_deps is exactly the union of the steps' uses;
   proof_origin describes the actual route. The restored node has the required source,
   searches, creation, blueprint, unit, and Lean records. Pass.

Second reading changed only this report by adding the independent audit. No Lean or node
repair was necessary. One public existence theorem is fully proved; zero holes are added,
and zero textual baseline holes are closed by this restoration.
