## What changed

The original target signature and docstring are unchanged. Its proof now obtains a finite
field with closed-subset descent and applies a proved, general topological criterion.
The two new modules are `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent` and
`Sheaf.AlgebraicGeometry.ClosedComponentDescentTopology`; both imports in the target are
proof-only. No existing definition, statement, visibility, or public import changed.

Repair of reviewer X-82c4d C1: populated all three `uses` lists and their
`proof_deps` union in `new-lem-sbc-finite-field-closed-component-descent` with
the seven existing nodes requested by the reviewer. These record the
non-elementary facts in the geometric proof plan. Lean statements and proofs
are unchanged by this metadata repair.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.exists_finite_intermediateField_component_preimages`.
Added hole: `AlgebraicGeometry.exists_finite_intermediateField_closed_component_descent`
(node `new-lem-sbc-finite-field-closed-component-descent`). This is a decomposition:
one upper hole closed and one lower hole added, net zero. The target still depends on
`sorryAx`; it is not a fully proved target.

`AlgebraicGeometry.component_preimages_of_closed_descent` is fully proved, with no new hole
(node `new-lem-sbc-closed-component-descent-topology`). Its axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. All three delivered files compile without errors or
warnings using lcompile.py. The target and geometric helper have only these axioms plus
`sorryAx`, from the one named, documented geometric hole. No data definition was added.

## No longer needed

No repository imports or old proof-dependency nodes are pruned: the original node's
`proof_deps` is empty. Removed the first worker's undelivered auxiliary modules
`FiniteIntermediateFieldForComponents` and `ComponentPreimagesForFiniteField`, and their
undelivered nodes `new-lem-sbc-finite-intermediate-field-coefficients` and
`new-lem-sbc-component-preimages-descent`. These were never library nodes, so their removal
is not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's `component_preimages_for_finite_intermediateField` is false.
STATEMENT-DISPUTED: a finite intermediate field need not define each geometric component.
Take k = R, X = Spec C, and L the bottom intermediate field. X has one component, but its
base change to the separable closure C is Spec(C times C), with two components. The full
inverse image of X is therefore not irreducible. Finiteness holds, so the counterexample
satisfies every hypothesis of that proposed helper.

The first worker's proved `exists_finite_intermediateField_for_components` only chooses
the bottom field; it expresses no coefficient collection or descent property. Its proof
cannot supply the missing invariance. Both helpers were removed from this delivery.
The new geometric hole requires actual simultaneous closed descent, without assuming that
an arbitrary finite field works or asserting the target's downstairs-component conclusion.

Searches also found the existing library theorem
`AlgebraicGeometry.exists_closed_subset_of_galois_invariant` in
`Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` (Stacks Tag 038B).
This supplies the invariant-closed-subset part of a future proof of the geometric hole,
but not the finite coefficient field and component invariance. It is recorded in that
node's proof plan; no unused proof import was added while this theorem remains a hole.
The topological step uses Mathlib's finite closed-cover criterion directly. LeanSearch
was unavailable; the attempted queries and actual Loogle, LeanFinder and grep searches
are recorded in searches.jsonl and the new nodes.

Sources checked directly: https://stacks.math.columbia.edu/tag/04KZ,
https://stacks.math.columbia.edu/tag/054R, and https://stacks.math.columbia.edu/tag/038B.
The Stacks source directory is absent on this machine. No change record is necessary:
all repaired helper statements are new, undelivered declarations.

## New nodes

`new-lem-sbc-finite-field-closed-component-descent` records the remaining geometric
coefficient-collection and closed-subset descent step. Its precise Lean signature, source,
complete mathematical proof plan, searches, chapter and unit are recorded. This is
strictly the descent step: it says nothing about maximality of the descended sets.

`new-lem-sbc-closed-component-descent-topology` records the fully proved criterion for a
continuous surjection whose finitely many upstairs components descend to closed subsets.
Its Lean proof builds a finite closed cover, applies the irreducible finite-cover lemma,
and uses maximality downstairs. No change records were added.

## Earlier second reading (a previous round; superseded)

1. Compared the target module with the repository using diff. The existing declaration's
   signature is byte for byte identical, including every binder and conclusion. Only two
   proof-only imports and the proof body change. The other two files are new modules.
   Verdict: pass after removing the false undelivered helper.
2. Compiled each file in import order using lcompile.py, and compiled a scratch copy with
   explicit #print axioms for all three declarations. The topology theorem has only the
   permitted three axioms; the target and descent helper additionally use sorryAx.
   There is exactly one sorry, in the named geometric theorem. No axiom, unsafe, opaque,
   implemented_by, extern, hollow definition, or data chosen from an unproved existence
   theorem appears. Verdict: valid decomposition, not a complete target proof.
3. Checked new statements and edge cases. The topological statement is proved in Lean and
   works for empty spaces. The geometric statement follows finite coefficient collection
   and Galois descent; for empty X use the bottom field. Unlike the rejected helper, it
   chooses a field with the required descent property. Searched Mathlib, the upstream
   library, Sheaf and DAG nodes using alternative wording; no exact duplicate was found.
   The existing invariant-closed-subset theorem is recorded for the unfinished step.
   Verdict: true intermediate statements, one geometric step still open.
4. The target is reduced from the top downward, using a direct Mathlib proof for the
   maximality argument and leaving only finite closed descent. All delivered imports serve
   signatures or proofs. The old proof_deps is empty, so the no-longer-needed list is
   complete. Read dag/units/sk-prop-normal-form.json: realized.statement and both
   realized.steps are empty in the repository; this below-unit refinement changes none
   of the unit's normal-form or slicing route. Verdict: route kept, no library pruning.
5. Updated the original node's proof, proof_deps and proof_origin to name the two actual
   intermediate declarations. New nodes have verbatim Lean signatures and all required
   fields, searches and mathematical proofs. No existing statement or definition changed.
   Verdict: DAG agrees with the repaired reduction.

Second reading changed: removed the false arbitrary-field descent statement and the
vacuous bottom-field helper; replaced them by genuine finite closed descent and a proved
topological maximality argument; repaired node metadata and report. One hole is closed
and one is added, so the delivery is explicitly a net-zero decomposition.


## Second reading by E1

1. Compared every delivered module with the repository. The target has exactly the old
   signature and docstring; its only edits are two proof-only imports and its proof body.
   The other two modules are new. No existing statement, definition, visibility, or public
   import changes, and no forced adaptation or change record is needed. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py. A scratch copy with three
   explicit #print axioms commands confirmed that the topological criterion uses only
   propext, Classical.choice and Quot.sound. The geometric helper and target additionally
   use sorryAx. The sole textual sorry is the entire proof of the named geometric helper;
   there are no definitions or forbidden declarations. Verdict: valid decomposition,
   with one upper hole closed and one geometric hole added, net zero.
3. Read Stacks Tags 04KZ, 054R and 038B directly and checked the two new statements.
   The geometric helper expresses simultaneous closed-subset descent, without the target's
   downstairs-component maximality conclusion. Affine charts must come from X itself;
   their base changes are stable under the automorphisms. Finite coefficient collection
   then fixes each chart ideal and its closure. Omega/L is Galois even for a nonnormal L/k.
   Empty X is covered by the bottom field; for Spec C over R the required field may be C,
   whereas the bottom field need not work. The proved topology theorem handles empty
   spaces and allows intersecting components, since its finite closed-cover argument
   does not require disjointness. New LeanFinder and Loogle searches with alternative
   wording, plus rg in Mathlib, upstream and Sheaf, found no replacement theorem. The
   existing Galois-invariant closed-subset theorem supplies precisely the invariant
   descent step but not finite coefficient collection. Verdict: true, smaller steps;
   the geometric hole cannot be closed in a few minutes with the available API.
4. Read the full topological proof: images of components form a finite closed cover;
   continuity makes each image irreducible; the Mathlib finite-cover criterion puts a
   downstairs component in one image; maximality gives equality; saturation identifies
   its full preimage. This removes a genuine maximality step from the geometric hole,
   so the hole is not a renamed target. All imports serve statements or proofs. The old
   proof_deps is empty, so no old dependency is missing from No longer needed. The unit
   sk-prop-normal-form has empty realized.statement and both realized.steps lists in the
   repository; this refinement changes none of its normal-form or slicing route.
   Verdict: pass, no library pruning.
5. Read all three nodes and the seven existing dependency statements of the geometric
   helper. Noetherian finite-type algebras and algebraic coefficient fields supply its
   first step; invariant closed descent supplies its second; faithful-flat surjectivity,
   base-change surjectivity and cartesian pasting supply its last. Their union matches
   proof_deps. The original node names the two declarations its Lean proof uses. New
   nodes include source, full signatures, searches, creation and blueprint records.
   Verdict: DAG agrees with Lean and the documented unfinished argument.

This second reading changed only the new geometric helper's docstring and matching DAG
proof text to specify affine opens of X, finite tensor coefficients, closure invariance,
and the Galois extension Omega/L; appended this independent review. Proofs and all Lean
signatures were retained. The earlier second reading remains historical, not this verdict.
