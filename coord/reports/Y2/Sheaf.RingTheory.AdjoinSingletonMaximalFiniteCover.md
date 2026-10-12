## What changed

Replaced the target hole in `exists_finite_cover_adjoin_singleton_atPrime` with a complete
Lean proof from the structural splitting-cover theorem `exists_finite_cover_adjoin_singleton_core`.
This new theorem has no analytic-unramified hypothesis or conclusion: it supplies local
presentations by generator-containing monogenic algebras. The target applies its original
`hLocal` to those presentations, then transports reducedness through the induced completion
isomorphism. Added proof-only imports of `AdjoinSingletonFiniteCoverCore`,
`AdicCompletionRingEquiv`, and Mathlib's local-ring ring-hom lemmas.

## Proved and sorry left

Closed the target hole `exists_finite_cover_adjoin_singleton_atPrime` and proved the private
transport helper `unramified_of_equiv`. Added one hole, `exists_finite_cover_adjoin_singleton_core`
(node `lem-weil-pbc-monogenic-maximal-finite-cover-core`). This is a decomposition, with net zero
holes closed. The new obligation is the algebraic construction and local presentations;
the analytic step is complete Lean using the supplied hypothesis. All sandbox modules compile
without warnings. Existing imported holes remain the responsibility of their own nodes.

## No longer needed

No existing node or module is pruned: the new construction node retains the original algebraic
proof dependencies. No existing public import was removed. The prior attempt's private
normal-open helpers were not in the current repository baseline and are not part of this delivery.
The exploratory analytic-descent theorem and normal-open theorem were discarded before delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the target itself as a hole. The structural construction is now stated
precisely with explicit local ring isomorphisms, and the target's use of its analytic hypothesis
is formalized. An exploratory statement claiming analytic descent for arbitrary finite covers
was discarded: the proof requires the local presentations supplied by the construction.
Edge cases: x=0 uses a positive-degree residue polynomial; the zero ring is excluded by domain
instances. Nonmaximal contraction to R causes no problem: coefficient lifts use R_n and finitely
many denominators outside n, not a claim that n is maximal. The construction does not choose
arbitrary existential data in any definition. The unit's fixed route is preserved.

## New nodes

`lem-weil-pbc-monogenic-maximal-finite-cover-core` states the algebraic part of Tag 0334 Step 5,
with the finite cover, normal open, and generator-containing local presentations. Its statement,
full source proof, and Mathlib search record are in its new module and node. No statement,
definition, public import or existing interface changes. No change record is required.

## Second reading by Y2

1. Compared the delivered target module with the repository baseline. Existing declaration
   signatures are byte-for-byte unchanged; only proof-only imports, a private helper, and the
   target proof were added.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds without warnings.
   The target proof contains no `sorry`, axiom, unsafe, opaque, extern, or hollow definition.
3. Checked the split core statement and node. It is a strictly simpler algebraic construction,
   has a source and proof docstring, and its remaining `sorry` is named and documented.
   No duplicate declaration was found in the repository or Mathlib search results.
4. The proof follows the unit route through the structural core and completion equivalence;
   imports are minimal for the proof and no prior node is pruned.
5. DAG `proof`, `proof_deps`, `proof_origin`, and Lean declarations agree, including the new
   core node and its module metadata.

Changed nothing during second reading beyond this report section; the delivered proof and core
decomposition are accepted.
