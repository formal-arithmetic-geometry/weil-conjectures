## What changed

Proved `AlgebraicGeometry.exists_subsingleton_H_one_tensor_proj_twist`, preserving its
signature, docstring and public imports. The proof applies closed-immersion Serre vanishing
and transports the conclusion using the existing polynomial Proj twist comparison.

Repair of the returned duplicate-theorem rejection: deleted the private
`AlgebraicGeometry.Scheme.Modules.finitePresentation_of_generators_kernel` theorem.
Added the proof-only `import all Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
and use its existing private `isFinitePresentation_of_generators_kernel` theorem directly.
Lean's module import-all mechanism makes this theorem available without changing its
visibility or any other module. The remaining private helper only reindexes finite local
generators and descends the finite presentations along the cover.

Updated the item's node proof, proof_deps and proof_origin to record the reused coherence
module. No new node, module, interface change or forced adaptation is included.
Local compilation of the repaired module passed without warnings in 6.9 seconds.
The prior second reading concerned the returned version and has been removed for a fresh
independent reading of this repair.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.exists_subsingleton_H_one_tensor_proj_twist`
(node `lem-sc-p1-proj-serre-h1-vanishing`).

The remaining private helper
`AlgebraicGeometry.Scheme.Modules.finitePresentation_of_finiteType_kernels` is fully proved.
No sorry remains in the delivered module and no new hole is added. This is a proof from
existing dependencies, not a decomposition. Existing imported results may still depend
transitively on project holes; the entire target closure is not claimed axiom-free.

## No longer needed

Removed direct proof imports relative to the original module:

- `Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists`: its node
  `lem-sc-p1-twist-exists` remains needed transitively through the twist comparisons.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: already exposed by the
  surviving imports and still used transitively.

The duplicate private finite-generator/kernel theorem is removed and its existing
counterpart is reused. `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian` and
`pqf-lem-coherent-ft-locnoeth` are retained; the returned version's pruning claim for them
was incorrect. The old direct `lem-pc-projective-space-serre-vanishing` dependency remains
used through the closed-immersion Serre wrapper recorded as `lem-pc-serre-vanishing`.
The unused coproduct clause of `proj_shifted_free_is_twist` does not prune its module:
its chart comparison is still needed. No global module-unreachability claim is made.

## Where the brief, the DAG or earlier work was wrong

The returned proof and prior second reading incorrectly treated the private existing
finite-generator/kernel theorem as unavailable. `import all` provides direct access in
Lean's module system. The repair imports and uses it, exactly as the return requests,
instead of repeating the same theorem under another name.

The inverse twist transport was already in the repository but absent from the original
node's dependency list. The repaired node retains this existing comparison. The unit's
realized statement and step lists are empty and the projective-space Serre route is retained.
The recorded `lem-pc-serre-vanishing` Lean declaration is the closed-immersion integer-twist
wrapper, although its natural-language statement describes powers of an ample module;
this proof uses the existing closed-immersion interface.

## Second reading by T2

1. Compared the sole delivered module with the repository using `diff -u`.
   The existing theorem's signature, docstring, visibility and public imports are
   byte-for-byte unchanged. Only its proof, proof-only imports and a proved private
   helper are changed. There are no definition changes or forced adaptations. Pass.
2. Independently compiled the module with `lcompile.py`: no errors or warnings
   (5.6 seconds). Searched the delivered source: no sorry or forbidden declarations,
   and no new definitions. A scratch copy with `#print axioms` gives only `propext`,
   `Classical.choice`, `Quot.sound` for the private helper, and those plus `sorryAx`
   for the main theorem, from existing imported project results. The helper's local
   generators are used inside a proof; no arbitrary existence witness is put into
   a data definition. Pass.
3. There are no split-off statements, new holes or new nodes. Read the existing
   private finite-generator/kernel lemma and checked the helper's finite-set
   reindexing, including the empty index set, kernel hypothesis and cover descent.
   Searched both library roots and Mathlib for coherent/finite-presentation and
   finite-generator/kernel results. The existing private construction is reused,
   rather than restated. The helper has a complete proof. Pass.
4. Read the Serre wrapper, shifted-free comparison and inverse twist transport.
   The isomorphism supplies a closed immersion; finite presentation supplies
   quasi-coherence. Degree one is positive. Pullback cancellation and tensor
   transport give exactly the requested cohomology group for all integer d,
   including zero and negative d, and the zero-module case poses no extra condition.
   Each proof import is used, while removed direct imports remain available through
   the stated dependencies where needed. Checked every old proof dependency:
   shifted-free comparison and coherence are retained; twist existence and
   projective-space Serre vanishing are used transitively, as the pruning section
   explains. The unit's realized lists are empty and its record is unchanged;
   the projective-space Serre route is retained. Pass.
5. Compared the node JSON with the repository. Only proof, proof_deps and
   proof_origin change. Their steps match the local helper, existing coherence
   construction, Serre wrapper and inverse twist transport in the Lean proof;
   proof_deps is precisely the union of the recorded uses. The statement and Lean
   signature record are unchanged. No new-node metadata is required. Pass.

Second reading changed no Lean proof or DAG data: the returned duplicate theorem
has already been removed correctly. Added this independent review and refreshed
only the scratch axiom check. One original hole closed, zero holes added; no
split-off statements and no globally pruned modules claimed.
