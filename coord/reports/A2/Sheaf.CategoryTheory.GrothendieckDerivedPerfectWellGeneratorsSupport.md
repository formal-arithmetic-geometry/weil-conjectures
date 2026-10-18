## What changed

Proved `CategoryTheory.exists_small_factorization_class_of_compact_localization` with its
original signature. The class is the essential image of complexes generated degreewise
below a sufficiently large regular cardinal. The proof constructs bounded roofs using the
already proved cover and acyclic swallowing lemmas, proves component-image coproduct
factorization, and chooses a uniform support bound using subobject lattices. All helper
lemmas are private and fully proved. No definitions or existing declaration signatures changed.

Updated the assigned node's proof, proof dependencies and proof origin to this construction.
Added ordinary proof imports for the source-library cardinal machinery and Mathlib's
fraction, filtered-colimit and mapping-cocone APIs. The existing derived coproduct cofan is
reused through an ordinary `import all`; its proof is not duplicated.

Moved the compact-generator telescope import from the support module to its sole direct
consumer, `Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGenerators`. The consumer's
only change is one ordinary import. Replaced the support module's general triangulated
subcategory import by the object-property shift import used in its statement.

Validation: both delivered modules compile together without warnings (5.9 s and 2.2 s).
A separate `#print axioms` check of the main theorem reported precisely `propext`,
`Classical.choice`, and `Quot.sound`. The original main signature was compared textually
with the delivered signature and is identical.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.exists_small_factorization_class_of_compact_localization`
(node `new-sfb-derived-perfect-well-generators-support-b4`).

Holes added: 0. Split-offs: 0. Sorries remaining in the item: 0. The adapted consumer
already had zero sorries and still has zero. This is a proof, not a decomposition.

## No longer needed

Removed from the item:

- `Sheaf.CategoryTheory.CompactGeneratorsBuildObjects`: the support construction does not
  use its telescope. Its direct consumer does, so the ordinary import now belongs there.
  Node `lem-pc-compact-generators-build-objects` remains needed by that consumer; it is not
  globally pruned and the unit's telescope route is retained.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`: replaced by
  `Mathlib.CategoryTheory.ObjectProperty.Shift`, the statement's actual dependency.

The proof does not use the canonical alpha-compact class, the maximal-class API, or
`derived_exists_perfectSmallClass_core` suggested by the old node's search comments.
No imports of `DerivedPerfectSmallClassCore`, `DerivedPerfectSmallClassCoreAlpha`,
`GrothendieckDerivedAlphaCompactRanks`, or `GrothendieckDerivedAlphaCompactClasses`
are needed here. These were not imports of the original item, and no global pruning of
those modules is claimed. The declared compact-localization dependency is used; the
alpha-small/factorization definitions are used exactly as stated. The derived-coproduct
node has been added as a proof dependency because its cofan proof is reused.

## Where the brief, the DAG or earlier work was wrong

The old search comments said to use `derived_exists_perfectSmallClass_core`. That theorem
is above this support obligation in the import graph: the import-direction tool reports a
cycle through the perfect well-generators theorem. The old one-step canonical-class plan
therefore did not supply an applicable theorem. The completed proof instead uses the
already proved bounded-complex, cover and acyclic-swallowing machinery in WeilConjectures.
The target statement is true and was not weakened. The old search-history fields are left
untouched under the existing-node field restrictions; the new proof and proof origin record
the route actually checked by Lean.

The assigned node is not a realized statement or step of `sk-cor-existence-ii`; that unit's
statement, steps, and reference route are unchanged. No source, unit or chapter is bypassed.

Delivery-tool failure observed after both modules and the axiom probes passed: preflight
refused the generated delivery with `uncommitted changes in the working tree`. The installed
`/home/ubuntu/weil-launcher/deliver3.py` writes `tools/stage3_gate.py` and
`tools/stage3_delivery.py` after making its delivery commit and before invoking preflight;
preflight checks for a clean working tree. This is an internal delivery-tool problem.
No tool or shared-repository file was changed by this worker. The required dry run was retried.

Resumed session, 2026-10-18: retained all proof work and checked it against the current
shared sources. The main theorem's signature is textually identical; the consumer diff
is exactly the one ordinary import above; both files satisfy the 100-character limit.
Rechecked downstream users and the prohibited cycle through `DerivedPerfectSmallClassCore`.
Ran the required dry run twice again. Both runs passed their compile and axiom-probe
phases and failed preflight solely with `(a) uncommitted changes in the working tree`.
Inspection of the installed delivery script confirms it still writes both gate scripts
after its delivery commit. This failure cannot be repaired by changing a Lean proof or
report in the sandbox. The maintainer must repair the delivery script, preserving its
checks and clean-tree invariant; AGENTS.md section 3 and tools/README.md reserve tool
changes to the maintainer. Nothing was pushed. All proof, node and change-record files
remain intact for another attempt after that tool repair.


Current resumed attempt (2026-10-18, 08:56 onward): the required initial dry run again
completed the compile and axiom-probe phases and failed preflight with exactly one reason:
`(a) uncommitted changes in the working tree`. Rechecked both current source files:
the main theorem signature remains textually identical, the consumer adaptation remains
exactly one ordinary import, both modules contain zero sorries, and all Lean lines are
within 100 characters. The installed delivery script still creates its commit at line 296,
then rewrites validation scripts at lines 299-310 before preflight at line 311. Those
rewrites also disable validation conditions (`and False` and `only_sorry` returning
`True`); they must be removed or corrected by the maintainer while preserving validation,
not committed or bypassed by a worker. No tool file has been edited by this worker.
The second dry run also completed compile and axiom-probe phases and failed with the
same sole clean-tree diagnostic. Nothing was pushed. Both required attempts in this
session reproduced the installed-script failure. The retained proof is unchanged and
ready for delivery once the maintainer repairs the delivery tool.

## Forced adaptations

`Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGenerators` was unclaimed. Compiling
its original source against the pruned support module failed at its telescope call:

```
GrothendieckDerivedPerfectWellGenerators.lean:55:6:
error(lean.unknownIdentifier): Unknown identifier `compactGenerators_buildObjects`
GrothendieckDerivedPerfectWellGenerators.lean:54:11:
error: Tactic `rcases` failed: `x✝ : ?m.253` is not an inductive datatype
```

The adaptation adds only `import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects`
before the existing support import. The adapted source compiles against the changed
support module. Every signature, visibility, proof and other line stays identical.
Change record: `coord/changes/A2-derived-perfect-support-imports.md`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
