## What changed

Implemented `AlgebraicGeometry.singleComplexOpenComparison_union` by applying the existing
`relativeMayerVietoris` to the source W = U union V. The proof constructs the restricted
square by pullback pasting, restricts the two complexes and explicitly constructs the
restricted coefficient morphism from the canonical derived pullback comparisons. Mathlib
proves compactness of W, qcqs of W → S, compactness of the two inverse-image opens and their
intersection, and the covering identity. `derivedPullback_tensor_preserve_QCoh` gives the
two quasi-coherent cohomology hypotheses. The final Mayer–Vietoris conclusion is
*definitionally* the original comparison on W.

Added one proof-only import for the new nested-open coordinate transport module, and one
for the existing derived pullback preservation theorem. Kept the existing relative
Mayer–Vietoris import and all statement imports. Updated the item's proof steps and
dependencies to agree with the Lean proof. No existing statement, definition, universe or
visibility changed; no other module was adapted.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.singleComplexOpenComparison_union`
(node `lem-pc-single-complex-open-union`), conditional on the imported statements.
No `sorry` remains in the item's module. Both delivered modules compile using
`lcompile.py --all` against the refreshed shared library (20.2 s and 22.7 s).

Added exactly one hole:
`AlgebraicGeometry.singleComplexOpenComparison_nested_isIso_iff`
(node `lem-pc-single-complex-open-nested-comparison`), in the new module
`Sheaf.AlgebraicGeometry.SingleComplexOpenNestedComparison`. Its proof is exactly
`:= by sorry`. Its docstring and node give the source and the full transport argument.

This delivery is a decomposition: one upper hole reduced and one strictly smaller
coordinate-transport hole added, net zero holes. The new theorem has no cover,
Mayer–Vietoris argument, local invertibility assumptions, quasi-coherence assumptions,
compactness assumptions or affine-base assumptions. The main proof uses it three times to
transport U, V and U intersection V, then performs the gluing using the existing
`relativeMayerVietoris`. It does not rename or repackage the union theorem.

The existing `AlgebraicGeometry.relativeMayerVietoris` remains a dependency with `sorry`;
its module and node were not changed. Other transitive dependencies retain their existing
status. The concrete restricted objects and coefficient arrow are constructed, with no
selection from a bare existence theorem.

Validation: the complete reduction and its new statement module compile cleanly with
`lcompile.py --all`. The earlier missing shared artifact is now available.

## No longer needed

None. The original relative Mayer–Vietoris route is retained. No original import, node or
module is pruned, and none of the unit's realized steps is bypassed. The unit record's
`realized` lists are empty; no unit record is changed. No new top-open comparison dependency
is needed: the final arrow is definitionally the ambient comparison on W.

## Where the brief, the DAG or earlier work was wrong

The original node had just one step which hid the nested-open coordinate transport needed
to apply Mayer–Vietoris after replacing X by U union V. That is isolated as the new theorem,
with no change to the union theorem's signature. The geometry and final comparison are
implemented directly; the final identification requires no additional naturality theorem.

The nearest-blueprint-ancestor helper returns None for this recently created module item,
because its creation record uses a module name. The new node therefore inherits the
explicit `blueprint.from.node` of the item's node (`lem-pc-rf-perfect-base-change`), keeping
its via chain and recording the precise source-open induction transport it serves.
Blueprint searches for “single complex open comparison”, “0DJ9” and “restriction”, and
project-source searches, found no existing node stating this coordinate transport.

The local `literature/stacks-project/` files are absent. The online Stacks texts of
[0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
[08HY](https://stacks.math.columbia.edu/tag/08HY) and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S) were read. The new transport proof is marked
as an agent's expansion of the source's canonical restriction identification. No literature
file was downloaded or edited. LeanSearch returned an Internal Server Error and is recorded
as unavailable; LeanFinder and Mathlib grep ran successfully, with no matching derived
coordinate-transport theorem.

Edge cases checked for the new statement: empty Z, empty W (forcing Z empty), Z = W,
W = top, arbitrary unbounded objects, arbitrary commutative squares and coefficient maps
which are not invertible. The canonical source and pullback identifications and conjugation
argument remain valid in all these cases; no cover or local-isomorphism premise is used.

## New nodes

`lem-pc-single-complex-open-nested-comparison`, in
`dag/nodes/sec-picard-framework/lem-pc-single-complex-open-nested-comparison.json`, states
invariance of invertibility under nested source-open restriction. Its single new module
is `lean/Sheaf/AlgebraicGeometry/SingleComplexOpenNestedComparison.lean`. It is the
coordinate-identification portion of the original plan, with its hypotheses written
explicitly and with canonical constructed coefficient data. The proof is left for a
subsequent stage-3 item. No change record is necessary because no existing interface changes.

The required `deliver3.py C1 Sheaf.AlgebraicGeometry.SingleComplexOpenUnion --no-push`
printed OK: the delivery compiles and passes preflight except for the second reading,
which belongs to the next worker. Nothing was pushed. The axiom probes reported no
forbidden axiom. This is a validated decomposition, with one original hole closed
and one strictly smaller hole added; it is not a proof independent of remaining sorries.

## Second reading by C1

1. **Existing interfaces: pass.** Read both delivered modules and diffed
   SingleComplexOpenUnion against the repository. The complete existing theorem
   signature, universes, visibility and statement imports are byte-for-byte unchanged.
   The changes are its proof, its explanatory docstring and two plain proof imports.
   The nested theorem is new; no existing definition or other module is adapted.
   Diffed the existing node too: only proof, proof_deps and proof_origin changed.
2. **Proof and axioms: pass as a decomposition.** Independently compiled both modules
   in import order with lcompile.py --all, without errors or warnings (16.1 s and
   15.9 s). Read the explicit restricted coefficient composite against the definition
   of singleComplexOpenComparison. The pullback pasting square, compactness instances,
   inverse-image cover and intersection, and the final relativeMayerVietoris application
   all use the actual stated hypotheses. Scratch-copy #print axioms probes for both
   delivered theorems show exactly propext, Classical.choice, Quot.sound and sorryAx.
   The only delivered sorry is the named nested theorem; there are no forbidden
   declarations or hollow definitions. The chosen composition comparisons are pinned
   by their left-derived universal property in exists_derivedPullbackComposition,
   not arbitrary existence witnesses. The remaining sorryAx dependence is explicit.
3. **Split statement: pass.** Read Stacks Tags
   [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
   [08HY](https://stacks.math.columbia.edu/tag/08HY) and
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S), and the declarations
   exists_derivedPullbackComposition and schemeDerivedBaseChange_pasting.
   Z <= W identifies the iterated source with Z and the iterated pullback with
   X-prime times_X Z. Coherent pullback comparisons identify the two restrictions
   and the explicitly constructed coefficient arrow; their adjoint mates identify
   the direct images. The counit transposes give the same arrow under these
   isomorphisms. This uses no cartesianness or geometric hypotheses. Checked empty Z,
   empty W (then Z is empty), Z = W, W = top, zero complexes and noninvertible phi;
   none invalidates these identifications. The lemma has no union, cover or three
   local invertibility premises and is strictly the transport part of the argument.
   Independently searched LeanFinder for Beck-Chevalley compatibility with iterated
   open restriction, Mathlib grep for conjugate composition and restrictFunctorComp,
   and both project roots for nested comparison and base-change restriction.
   Results give underived restriction identities and generic mate calculus, not this
   derived theorem. Read the proved upper-left transport exists_derivedBaseChange_top_iso:
   it handles only one vertex and does not supply the simultaneous nested source
   and coefficient transport. Closing the new hole requires that additional mate
   calculation; no few-minute replacement was found. Its node, source and complete
   written proof are present.
4. **Top-down route and pruning: pass.** The main proof applies the existing relative
   Mayer-Vietoris theorem after constructing W = U union V, uses the new transport
   exactly on U, V and their intersection, and uses the existing QCoh preservation
   theorem on the two explicit restrictions. Its conclusion unfolds directly to the
   desired ambient comparison. Each added plain import is used; the public imports
   supply notions in the unchanged signature. The sole old proof dependency, relative
   Mayer-Vietoris, is retained, so No longer needed correctly says none. Read
   dag/units/sk-thm-picard-semicon.json: realized.statement is [] and realized.steps
   is [[]]. This delivery changes neither that record nor its route.
5. **DAG agreement: pass.** The union node steps match the geometry, QCoh restriction,
   three transports and final gluing in Lean, and proof_deps is exactly the union of
   their cited nodes. The new node records the explicit coefficient data and the same
   iff as its Lean signature, with source, proof_origin, search records, creation,
   blueprint ancestry, chapter/unit and verbatim lean.statement. It leaves precisely
   the named transport theorem open, not a restatement of the union theorem.

Second reading changed the nested theorem's docstring and its node proof step to
name the two coordinate isomorphisms e and e-prime explicitly, and to specify that
adjunction-unit cancellation concerns these isomorphisms. In particular it does
not assert invertibility of the unit for W -> X. No Lean proof or signature changed.
One original hole is closed and one smaller hole is added: net zero, decomposition.
