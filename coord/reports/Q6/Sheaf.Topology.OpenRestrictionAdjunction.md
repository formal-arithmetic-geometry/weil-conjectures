## What changed

Proved `TopologicalSpace.Opens.exists_openRestrictionAdjunction` in
`Sheaf.Topology.OpenRestrictionAdjunction` without changing its statement, definitions,
public imports, or universes. Use Mathlib's `SheafOfModules.overPushforwardOverAdj U`;
the forward and inverse component identities both close by `rfl` after introducing
the quantified arguments. Thus this proves the specified adjunction and both formulas,
not merely existence of an unspecified adjunction.

Removed the unused private imports `Sheaf.CategoryTheory.RingedSiteModules` and
`Sheaf.CategoryTheory.SiteCoveringAxioms`. Updated the item's DAG node's `proof`,
`proof_deps`, and `proof_origin` to the Mathlib specialization and the two definitional
computations. No interface or definition changed, so no consumer adaptation or change
record is necessary. The unit `sk-thm-p1` and its realized statement and steps are preserved.

Validation: two successful server single-file compilations, including a compile after
removing the imports. A temporary `#print axioms` probe reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; the probe is removed from the delivered file.
The argument applies uniformly to the empty open, the whole space, and opens disjoint
from U, since it specializes the arbitrary-object slice adjunction and uses no
nonemptiness or strict-inclusion assumptions.

## Proved and sorry left

Closed one existing hole:
`TopologicalSpace.Opens.exists_openRestrictionAdjunction`
(node `lem-weil-pbc-ringed-space-open-restriction-adjunction`).

Holes closed: 1. Holes added: 0. Split off: 0. Sorries left in the item: 0.
No sorries are added elsewhere. The theorem is proved using only the standard axioms,
not by invoking either of the still-unproved planned intermediate theorems.

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.

The item's proof no longer needs either planned proof dependency:

- `lem-weil-pbc-open-module-section-functors`, module
  `Sheaf.Topology.OpenModuleSectionFunctors`, declaration
  `TopologicalSpace.Opens.open_module_section_functors`.
- `lem-weil-pbc-open-module-transpose-morphisms`, module
  `Sheaf.Topology.OpenModuleTransposeMorphisms`, declaration
  `TopologicalSpace.Opens.exists_openModuleTransposeMorphisms`.

Neither module is imported, and both edges are removed from the item's `proof_deps`
and proof-step `uses`. Their separate sectionwise construction is subsumed here by
Mathlib's already constructed adjunction. These are dependencies pruned from this
proof; no assertion is made that other consumers cannot need them, and neither their
Lean files nor their nodes are deleted. The two existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier Mathlib search records judged the slice adjunction to require further
comparison and component calculations. The current Lean statement already uses exactly
the slice-site functors `overFunctor` and `pushforward (pushforwardOver U)`, so no
comparison with the topological subspace is required. Mathlib's adjunction is already
the required witness, and both component formulas are definitional equalities.
The planned six-step construction and its two split dependencies are unnecessary for
this item. The theorem statement and its mathematical content are correct and unchanged.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
