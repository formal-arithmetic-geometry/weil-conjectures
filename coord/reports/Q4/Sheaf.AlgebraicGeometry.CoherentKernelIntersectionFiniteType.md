## What changed

Proved `AlgebraicGeometry.coherent_kernel_intersection_finiteType` in
`Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType` without changing its
signature. Added the proof-only import
`import all Sheaf.AlgebraicGeometry.CoherentKernelConditionRestriction` to reuse
its proved private finite-type transport helpers and restriction equivalence.
The proof constructs the fixed-rank map on the preimage open of U, applies hK,
compares kernels, and transfers finite type through the iterated-slice equivalence.
Updated the existing node's proof, proof_deps, and proof_origin to describe this
argument. No definitions, interfaces, or target statements changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.coherent_kernel_intersection_finiteType`
(node `lem-weil-pbc-coherent-kernel-intersection-finite-type`).
No sorry remains in the item, and no hole was added or split off.
The reused helper declarations have complete proofs. The delivery dry run checks
all declaration axioms against propext, Classical.choice, and Quot.sound.

## No longer needed

None. The proof retains the three original statement imports and both original
proof dependency nodes. It adds the kernel-condition restriction node for its
proved transport helpers. No new module or node is needed. The item's node is
below the unit level, and no realized unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical argument in the node is correct, but its Lean glue was missing:
finite type must be transported through the open-slice equivalences and the
iterated-slice equivalence, rather than identified definitionally across their
sites. Existing proved helpers in CoherentKernelConditionRestriction supply this
transport. The sectionwise evaluation proof supplies kernel preservation for
overMap. Category-level finite limits avoid typeclass timeouts on the explicitly
constructed composite map. The theorem uses a documented 400000 heartbeat budget
and still compiles within the single-file 60-second limit.

The argument applies unchanged to an empty intersection and n = 0: mapFreeIso
uses the same index type, and no nonemptiness, cover, surjectivity, or finite-type
hypothesis on F is introduced. No new statement requires an edge-case audit.

## Second reading by Q4

1. **Unchanged interface — pass.** Read the original and delivered module and
   their diff. The sole existing declaration's entire signature, from `theorem`
   through `:= by`, is byte-for-byte identical. All hypotheses match the node:
   an arbitrary scheme and module, two arbitrary opens, a fixed rank n, the
   kernel condition on every open of U at precisely that rank, and an arbitrary
   map on W. The conclusion is finite type of the iterated-slice restriction of
   its kernel to W intersect U. No cover, surjectivity, finite type of F, or
   nonemptiness was added. No definition or public import was changed.
2. **Proof and axioms — pass.** Local single-file compilation produced no error
   or warning (37.7 seconds). Read the transported source/target isomorphisms,
   the application hK V g, the sectionwise kernel preservation argument, and
   the iterated-slice comparison. There is no sorry or prohibited declaration
   in the delivered module. The scratch copy's explicit `#print axioms` check
   confirms only propext, Classical.choice, and Quot.sound. The imported private
   transport helpers and restriction equivalence have actual constructions
   and complete proofs; no arbitrary data is chosen from an unproved existence
   theorem.
3. **Split statements — pass (none).** No new declaration, node, or hole is
   introduced. Checked empty intersections, U or W empty, and rank zero: the
   same preimage/image identities and rank-preserving mapFreeIso apply without
   a positivity or inhabitedness assumption.
4. **Shortest route, imports, unit — pass.** Independently searched LeanFinder
   for finite generation through open slice equivalences and kernel restriction,
   and searched Mathlib, lean/Sheaf, and lean/WeilConjectures for alternate
   finite-type and kernel transport results. No direct theorem closes this
   statement. Existing Mathlib kernel isomorphisms and existing proved private
   finite-type helpers are reused rather than duplicated. The new `import all`
   is proof-only and is needed to access those private helpers; the original
   public imports support the statement's scheme/open and generator notions.
   Both old proof dependencies remain used; No longer needed is complete. Read
   dag/units/sk-thm-p1.json, including realized: this node is below unit level,
   and no realized statement or step or chapter route is bypassed.
5. **Node agreement — pass.** Compared both JSON files: only proof, proof_deps,
   and proof_origin changed. Read the records of the original dependencies and
   the restriction module's helpers. The three proof steps match the actual
   Lean construction and the union of uses equals proof_deps. The additional
   restriction node accounts for reused helpers, not an application of its
   stronger all-ranks theorem. Its source attribution is retained. No new-node
   field checks or statement-change record are needed.

Changes by the second reader: added this independent review and its search
evidence. No Lean or DAG repair was necessary. Holes closed: one,
AlgebraicGeometry.coherent_kernel_intersection_finiteType. Holes added: zero.
