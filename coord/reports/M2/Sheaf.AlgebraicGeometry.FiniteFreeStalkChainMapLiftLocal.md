## What changed

Replaced the `sorry` in `AlgebraicGeometry.Scheme.Modules.exists_chainMap_of_stalk_local`
with a reduction to two separate parts of the existing finite-matrix proof plan.
Added proof-only imports of `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseLift`
and `Sheaf.AlgebraicGeometry.FiniteFreeStalkDegreewiseShrink`. Existing signatures,
definitions, public imports, and visibility are unchanged.

The first new theorem extends an arbitrary family of degreewise stalk maps without
assuming or concluding any differential equations. The second starts with a family
already defined on an open and shrinks away its differential-commutativity defects.
The item's proof uses the original chain map to verify the second theorem's stalk
equations, constructs a chain map with `CochainComplex.ofHom`, and checks its stalk
comparison degreewise by cancelling the two inverse-comparison pairs. These are
strictly separate portions of the original argument, not a renamed copy of it.

Updated the item's DAG proof and dependencies to this reduction. Added one node
and one statement module for each of the two remaining portions. No unit route
changed; `sk-thm-picard-perfect.realized` has no bound nodes bypassed by this reduction.

## Proved and sorry left

Closed the item's one hole, `AlgebraicGeometry.Scheme.Modules.exists_chainMap_of_stalk_local`
(node `lem-pc-finite-free-stalk-chain-map-lift-local`), conditionally on the two
intermediate statements. Added two holes:

- `AlgebraicGeometry.Scheme.Modules.exists_degreewise_of_stalk_local`
  (`lem-pc-finite-free-stalk-degreewise-lift`).
- `AlgebraicGeometry.Scheme.Modules.exists_shrink_degreewise_comm_of_stalk`
  (`lem-pc-finite-free-stalk-degreewise-shrink`).

This is a decomposition, not a proof of the underlying finite-matrix extension
from Mathlib, and has net holes closed minus added equal to -1. The item's proof
contains no `sorry`; each new module has exactly its one named public theorem
with `:= by sorry`, a source, and a complete proof in words.

Edge cases checked in the new statements: empty or disjoint degree intervals,
zero source or target terms, rank-zero free terms, an empty coefficient list,
and an already commuting degreewise family. Empty intersections may be taken
as the whole scheme for the lift and as the given open for the shrinking step.
No assumptions of nonzero rank, nonempty support, or reducedness are used.

## No longer needed

None. Both original public imports remain necessary for the unchanged statement.
No original node or module is pruned from the transitive proof route. The original
free-module and module-stalk dependencies now occur in the two new nodes rather
than directly in the item's proof, so they are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The three original proof dependencies supply definitions and the restriction/stalk
comparison, not statements extending matrices or shrinking their defects. These
missing steps have therefore been stated as two genuine parts of the plan.

The local compiled cache lacked `Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso.olean`
at the first compilation attempts. The mandated `lcompile.py --all` failed before
elaborating the new modules. No missing dependency was copied into the sandbox or
compiled as a workaround. Isolated Mathlib tests in `scratchpad/` check chain-map
commutativity under conjugation, `CochainComplex.ofHom`, degreewise functor mapping,
and the comparison inverse cancellations; these tests are outside the delivered
`lean/` tree. The complete assembly also compiles in
`scratchpad/ConcreteSignatureAssembly.lean` with the comparison supplied as an
abstract parameter; this checks both intermediate signatures and every line of
the reduction without constructing or compiling the missing dependency. It does
not replace validation against the actual canonical comparison.

The initial delivery dry run failed in local compilation before preflight for
the same missing object file. After the cache supplied that dependency,
`lcompile.py --all` compiled all three concrete modules cleanly: the two new
statement modules and the item's completed reduction. The report retains the
initial cache failure to explain the isolated tests; it is now resolved.

## New nodes

`lem-pc-finite-free-stalk-degreewise-lift`, in
`lean/Sheaf/AlgebraicGeometry/FiniteFreeStalkDegreewiseLift.lean`, states the finite
coefficient-extension step before any chain equations are imposed. Its proof
uses finite bases, bounded support, germ representatives, and the canonical
stalk comparison.

`lem-pc-finite-free-stalk-degreewise-shrink`, in
`lean/Sheaf/AlgebraicGeometry/FiniteFreeStalkDegreewiseShrink.lean`, states the
zero-germ differential-defect step for an already defined degreewise family,
including compatibility of its stalk after further restriction. It extends no
prescribed family from the stalk. Its proof intersects the finitely many
vanishing neighbourhoods and uses restriction/pullback composition.

No change records are needed: no existing statement or definition was changed
and there are no forced adaptations.

## Second reading by M2

1. Compared the delivered item module with the repository version. The existing declaration signature and all definitions are byte-for-byte unchanged; only proof-only imports and the proof body differ. Verdict: pass.
2. Compiled all three delivered modules with the mandated `lcompile.py --all`; compilation is clean. The item has no `sorry`; each new statement module contains only its named, documented split theorem with `sorry`. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked the two split-off statements against their DAG nodes, source text, and edge cases. The degreewise lift omits chain equations, while the shrink theorem starts from an existing family and preserves its stalk comparison; both are strictly smaller than the item and have complete proof descriptions. Searches recorded in the nodes found no duplicate library theorem. Verdict: pass.
4. The proof follows the planned route through degreewise extension, defect shrinking, and `CochainComplex.ofHom`; the unit route and realized unit are preserved. Proof-only imports are minimal for the completed reduction, and no old dependency can be removed. Verdict: pass.
5. Updated DAG proof/proof_deps/proof_origin data matches the Lean proof, and each new node's Lean record matches its declaration. Verdict: pass.

Changed after review: no proof or statement changes were necessary; this section records the checks above.
