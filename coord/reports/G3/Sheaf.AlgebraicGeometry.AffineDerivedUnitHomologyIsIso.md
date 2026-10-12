## What changed

Repair of the landing refusal: replaced the duplicate private
`AlgebraicGeometry.tilde_preservesKernel` in the new comparison module by the
strictly more general private theorem `preservesKernel_of_iso_image`. Its binders
are arbitrary categories with zero morphisms, a fully faithful functor preserving
zero morphisms, a morphism, and an isomorphism from an image object to the target
kernel. It has no ring, affine scheme, or quasi-coherence assumptions. The affine
proof supplies this isomorphism using the quasi-coherent kernel counit. This is a
categorical generalization, not the old statement with an equality parameter.
The existing theorem named in the return is private and cannot be used through an
ordinary import, so the repair takes the permitted generalization route.

Proved `AlgebraicGeometry.affineDerivedUnit_homology_isIso` with its signature and
visibility unchanged. Added the proved module
`Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso` for the canonical
comparison from termwise sections to derived sections on a complex of associated
sheaves. The main proof factors the canonical derived unit on homotopy objects,
uses essential surjectivity of Qh, descends hF through Q, restricts the canonical
adjunction to D_QCoh, and transports its unit using uniqueness of right adjoints.
Finally homology preserves the resulting isomorphism.

The new theorem proves its comparison using affine acyclicity, the existing
bounded-below acyclic-unit theorem, compatibility with the unbounded derived
functors, the affine lower-truncation theorem, and naturality. This avoids having
to identify arbitrarily selected homology comparisons with the adjunction unit.
The main module proves kernel preservation locally inside the target proof; the
new comparison module uses the general categorical kernel lemma instead of
repeating the affine lemma as a new declaration.
No definition, existing statement, public import, or other module was changed.

Validation: the full sandbox compiles through lcompile.py. The required deliver3.py
--no-push dry run is the final check. Edge cases checked in the argument: arbitrary
integer degree, genuinely unbounded complexes, the zero ring, and zero objects.
No finite-generation or boundedness hypothesis is used.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affineDerivedUnit_homology_isIso`
(node `new-affine-derived-unit-homology-isIso`).

Also proved the new theorem
`AlgebraicGeometry.affineTildeDerivedSectionsUnit_isIso`
(node `new-affine-tilde-derived-sections-unit-isIso`).

Original holes closed: 1. New holes added: 0. No sorry remains in either delivered
module; the new private helpers are proved. Existing imported holes are unchanged.
This is a proof from existing library declarations, not a decomposition with new
unproved statements.

## No longer needed

Removed the item's proof import
`Sheaf.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison`
(node `lem-pc-affine-derived-sections-homology-comparison`). Its arbitrary natural
homology comparison is not used by this proof. The underlying affine truncation
result remains needed and is imported by the new module.

The old proof_deps entry `lem-pc-affine-derived-tilde-homology-comparison`
is removed (it is a nonexistent ID; its actual counterpart is the following node).
The original planned tilde homology comparison is also unnecessary as an imported
module: `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`
(node `new-affine-derived-tilde-homology-comparison`). The proof establishes exactness
locally and uses the source library's exact-functor homology and truncation tools.
`Sheaf.AlgebraicGeometry.AffineDerivedSectionsTruncatedBottom`
(node `new-affine-derived-sections-truncated-bottom`) is not needed by this route;
the bounded-below acyclic-complex theorem supplies the starting case instead.
These are local dependency removals, not a claim that the modules are unreachable
from every other target branch. The ordinary tilde-sections adjunction and
quasi-coherent kernel result remain needed. The unit's realization record is
unchanged; this is a change below the unit level.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was rejected because the new comparison module still
repeated the private affine kernel lemma word for word. The earlier repair only
changed the main module. This repair changes the offending new module itself and
updates its node to record the categorical generalization and affine specialization.

The original node named `lem-pc-affine-derived-tilde-homology-comparison`, which does
not exist. The actual node is `new-affine-derived-tilde-homology-comparison`.
The original single proof step also hid compatibility of the derived unit with
chosen natural homology comparisons. The proved route uses canonical derived-unit
factorization and naturality, so it does not assume that compatibility.

The literature payload is absent in this clone; read the cited proof directly at
https://stacks.math.columbia.edu/tag/06Z0. The generic blueprint ancestor tool returns
None for this item's created.item chain (the creation records use module names),
so the new node follows the existing parent chain explicitly back to the blueprint
node lem-pc-projection-formula. Searches over the whole blueprint for 06Z0,
associated sheaf, and derived global sections found no duplicate statement.
LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder and
Mathlib grep found no exact theorem; the source-library bounded-below and exact-
functor results are used in the proof.

## New nodes

`new-affine-tilde-derived-sections-unit-isIso`, in
`dag/nodes/sec-picard-framework/`, records the canonical sections comparison on a
homotopy complex of associated sheaves. Its theorem is fully proved in the new
module, including the unbounded truncation step. This is a concrete part of the
module-unit calculation and does not restate the original theorem about arbitrary
F, G, adj, hF, hG, M, and n. No change record is necessary: all existing interfaces
are unchanged and the new module is imported only for proofs.

## Second reading by G3

1. Interface check: PASS. Diffed both delivered modules against the repository
   (the comparison module is new). The existing theorem's signature is byte for
   byte identical, its visibility is unchanged, and its five public imports are
   unchanged. There are no definition or statement changes, forced adaptations,
   or change records. The existing node differs only in proof, proof_deps, and
   proof_origin. The existing transitive import change record
   LowerTruncationStepTriangleProofImports requires no adaptation here.
2. Proof check: PASS. Both modules compile with lcompile.py, without warnings.
   Neither contains sorry, axiom, unsafe, opaque, implemented_by, or extern;
   neither constructs data from an arbitrary unproved existence theorem.
   Explicit scratch #print axioms checks on both public theorems give only
   propext, Classical.choice, Quot.sound, and sorryAx. The latter comes from
   existing imported open statements; this delivery adds no holes. The delivery
   tool additionally probes every delivered declaration.
3. New statements: PASS. No statement is split off with sorry. The new proved
   comparison theorem is a strictly separate component: its input is a homotopy
   complex, and its conclusion is about the canonical sections comparison, with
   no F, G, adj, hF, hG, or homology degree from the target. The generic private
   kernel lemma reflects a genuine lifted limit fork and needs no abelian or
   affine hypotheses. Checked zero objects, zero ring, every integer degree,
   and arbitrary unbounded complexes: boundedness is introduced only for the
   truncation object, never imposed on the input. Independent searches used
   acyclicity/unit and kernel-in-essential-image formulations via msearch grep,
   Loogle, and LeanFinder, plus rg over both source roots. Kernel-comparison and
   reflection lemmas exist and are used; no public exact replacement was found.
   The existing affine kernel helpers are private. Read the cited module-unit
   calculation directly in https://stacks.math.columbia.edu/tag/06Z0.
4. Route and pruning: PASS. Read the bounded-below acyclic-unit theorem and the
   affine truncation statement. The proof uses canonical unit factorization,
   bounded-below compatibility, truncation, naturality, and uniqueness of right
   adjoints; it does not assume compatibility of arbitrary selected homology
   comparisons with the unit. The removed old proof dependencies are accounted
   for above, including the invalid old tilde-comparison ID. The unit record
   sk-thm-picard-f-representable has empty realized statement and step lists;
   it is unchanged and no recorded realization is bypassed. All added imports
   are proof-only; the new module's public imports support its statement.
   Tested removing MapDerivedCategory: compilation specifically failed on
   rightDerivedFunctorCompMapDerivedCategoryIso, so that import is necessary
   and was restored.
5. DAG agreement: PASS. Checked each step against the Lean proof, the exact
   union of uses against proof_deps, and existence of every referenced node.
   The new node has statement dependencies, source, full proof, proof_origin,
   three search records, creation/blueprint/chapter/unit metadata, and the
   verbatim Lean signature. No unit or existing statement metadata is changed.

Second-reader repairs: replaced the stale target proof docstring by the actual
canonical-adjunction route. Removed the private tilde_preservesKernel_aux
(the old affine kernel theorem with an equality parameter) and placed its
kernel-fork argument directly inside the target proof, so the delivery adds no
duplicate affine-kernel declaration. Updated this report accordingly. The
mathematical route, all existing signatures, and the new comparison theorem
remain unchanged. Holes closed: affineDerivedUnit_homology_isIso (1 of 1).
Holes added or left in delivered modules: none. New split-off holes: zero.
