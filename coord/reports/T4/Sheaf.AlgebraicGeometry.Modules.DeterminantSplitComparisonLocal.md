## What changed

This verifies the still-queued repair for upstream review #1428, rather than closing a new
hole. In determinant_split_comparison_restriction, replace the two rewrites and exact with
`simpa only [hd] using hn W Z hW hZW y`, making the substitution a single explicit step.
No other Lean text changes.

The current determinant_split_comparison_local obtains the unique linear family from
DeterminantSplitLinearMaps, applies DeterminantSplitLinearBijective, and converts the resulting
bijective maps with LinearEquiv.ofBijective. The generator formula is definitionally unchanged.
The current determinant_split_comparison_restriction substitutes hd on both sides of hn using simpa only.
Its signature already contains dNatural, hn and hd; the unconstrained tuple family c is gone.
Both signatures, visibility, imports, and DAG routes are preserved.

The assigned module compiled cleanly with lcompile.py. LeanFinder and Loogle searches confirmed
LinearEquiv.ofBijective and its forward-map equation; the existing proof already uses that route.

## Proved and sorry left

Holes closed by T4: none (0 of 0). Holes added: none. No sorry remains in the assigned module.
The existing complete proofs are
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local
(node new-determinant-split-local) and
AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction
(node new-determinant-split-restriction).
No intermediate statements were split off.
This verification claims no net proof progress and does not claim that dependencies are sorry-free.

## No longer needed

None. Both proof-only imports remain necessary for the local existence proof.
No module or node is pruned and no public import changes.

## Where the brief, the DAG or earlier work was wrong

The brief says the assigned module still contains sorry, but its current source contains none.
coord/repairs.txt still lists the old #1428 unconstrained-c counterexample. The landed repair
records determinant_split_comparison_restriction.md,
determinant_split_comparison_restriction_hypotheses.md, and
determinant-split-restriction-right-inverse.md already document the corrected interface.

In the old Spec(Z), ranks (0,1,1) counterexample, sectionwise rescaling is not natural.
The current hypotheses hn and hd explicitly exclude that family: substituting hd into hn
is precisely the required restriction equation. This also works for empty opens, zero rings,
and rank zero, without cancellation or additional rank assumptions.

The caller DeterminantSplitComparison retains naturality from the linear construction, so the
repair does not merely assume the desired property of an arbitrary constructed equivalence.
No further statement correction or forced adaptation is needed. The two current node proofs
agree with these Lean arguments. The stale queue entry should be retired by the maintainer.

## Second reading by T4

1. Interface preservation: PASS. Compared the complete sandbox module with the repository
   using diff. The sole change replaces `rw [hd, hd]; exact hn W Z hW hZW y` by
   `simpa only [hd] using hn W Z hW hZW y`. Both existing signatures, all docstrings,
   visibility and imports are byte-for-byte unchanged. No definitions or targets change.
2. Proof validity: PASS. Compiled the delivered module cleanly with lcompile.py. Compiled
   a separate scratch copy with #print axioms for both full declaration names: each uses
   only propext, Classical.choice and Quot.sound, with no sorryAx. The delivered source
   contains no sorry, axiom, unsafe, opaque, implemented_by, extern or kernel-check bypass.
   The local proof takes d from the unique natural-family theorem, not an arbitrary
   undetermined existence witness. Local bijectivity supplies only a property of d;
   LinearEquiv.ofBijective preserves its forward function definitionally.
3. Split statements: PASS, vacuous. There are no new statements, modules, nodes or holes.
   Read the imported linear-map existence and local-bijectivity signatures: the first
   supplies exactly hd, and the second applies with all the supplied splitting and rank
   hypotheses. Naturality transfer substitutes hd at W and Z and then uses hn. It does
   not require cancellation, nonzero rings, positive ranks or nonempty opens, so these
   edge cases introduce no exception. No new search obligation for split statements arises.
4. Route and pruning: PASS. Read both existing dependency modules and the caller
   DeterminantSplitComparison.lean. The local proof uses both proof-only imports directly;
   all public imports supply types or notation in the signatures. Searched the local
   determinant modules and Mathlib linear-equivalence files and checked the first worker's
   LeanFinder/Loogle results: ofBijective is already the direct conversion route. The
   restriction proof needs only equality substitution. No old proof dependency is unused.
   Read dag/units/sk-thm-picard-rr.json: its realized statement and step lists are empty
   and remain unchanged; this delivery bypasses no realized unit step. The external
   literature markdown named by proof_origin is absent locally; the existing node statements,
   proof steps, unit record and landed correction records were available and read.
5. DAG agreement: PASS. Read new-determinant-split-local and
   new-determinant-split-restriction. The local node's three steps match unique linear
   construction, local bijectivity and ofBijective, with exactly the two recorded proof_deps.
   The restriction node records substitution into hn, with empty proof_deps, exactly as
   implemented. Both stored Lean statements agree with the unchanged delivered signatures;
   proof_origin remains appropriate. No node edits are necessary.

Second reading changed only this report: no further Lean repair was needed. Zero holes
closed, zero holes added, zero statements split off, and no pruning. The axiom check also
establishes that both delivered declarations currently have no transitive sorryAx dependency.
