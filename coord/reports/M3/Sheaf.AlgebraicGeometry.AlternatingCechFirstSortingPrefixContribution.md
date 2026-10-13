## What changed

Proved `AlgebraicGeometry.Scheme.cechFirstSortingJunctionPrefixContribution`
without changing its signature or any definition. Two proved private helpers
identify the unique prefix-labelled deletion and show that deleting it recovers
`τ`. The main proof collapses that finite sum, composes restrictions using
thinness of `X.Opens` and `Functor.map_comp`, cancels the two integer signs,
and handles failed sorting filters by zero summands. The existing public import
of `AlternatingCechSortingOperators` is required by the statement and remains.
The node proof and proof origin now describe this direct computation.

An earlier candidate's duplicate private `prefix_restriction_comp` helper was
removed before this reading; composition is a local equality in the main proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.cechFirstSortingJunctionPrefixContribution`
(node `lem-pc-alternating-cech-first-sorting-junction-prefix-contribution`).
Added zero holes. No sorry remains in any delivered module and no statement
was split off. This is a proof, not a decomposition: 1 of 1 original holes closed.

## No longer needed

None of the original imports, proof-dependency nodes, or modules was removed.
Both original proof dependencies, `def-pc-alternating-cech-sorting-operators`
and `def-weil-pbc-site-cech-complex`, remain used. The earlier candidate's
duplicate private composition helper is unnecessary; it was not in the
repository baseline and its removal is not module pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier candidate introduced a private theorem duplicating the private
`AlgebraicGeometry.Scheme.sortingRestriction_comp` of the nonjunction
cancellation module. The candidate was already repaired to use a local equality.
The incoming report described that repair rather than the full change against
the repository's sorry-containing baseline; the second reading corrected it.
No statement or definition change, forced adaptation, or change record is needed.

## Second reading by M3

1. PASS: Compared the delivered module with the repository using `diff` and
   checked the complete existing theorem signature byte for byte. It is
   identical. The import and visibility are unchanged, no definition is added
   or changed, and no other Lean module is delivered.
2. PASS: Compiled the delivered module with `lcompile.py --all` (2.5 seconds,
   no errors or warnings). Compiled a fresh scratch copy of the delivered text
   with `#print axioms` for both private helpers and the public theorem
   (3.0 seconds). Helpers use only `propext`, `Quot.sound`; the public theorem
   uses only `propext`, `Classical.choice`, `Quot.sound`. No sorry, axiom,
   unsafe, opaque, implemented_by, extern, or kernel-check bypass occurs.
3. PASS: No split-off statement or new node exists. Read both private helper
   proofs: the filter uses permutation injectivity and the deletion uses the
   fixed prefix plus the tail branch. Independently exhausted 74,420 cases
   over all permutations and all positions for sizes 2 through 5; both
   identities hold, including first/last positions and degree p=0.
   Repeated tuple values are irrelevant because these identities use labels.
4. PASS: The proof takes the direct finite-sum route and needs only the one
   existing statement import. Fresh LeanFinder search for singleton sums and
   Loogle search for `Finset.sum_ite_eq` found generic ingredients, already
   handled by `Finset.sum_ite_eq'` in the proof. Searched Lean sources for
   junction deletion and partial sorting; no public generic helper or shorter
   complete theorem was found. The repeated-face deletion theorem is only
   an identity-permutation special case; the composition helper in the
   nonjunction module is private. Both old DAG dependencies remain used,
   so No longer needed is complete. Read `dag/units/sk-thm-picard-pn.json`;
   its realized fields are empty, and this local labelled computation changes
   neither the unit's statement nor its route.
5. PASS: Compared node JSONs; only `proof` and `proof_origin` differ. The
   four proof steps match the helper identities, local restriction transport,
   sign cancellation, and finite-sum assembly. The union of their uses is
   exactly the unchanged `proof_deps`. No new node requires additional fields.

Second reading changed only this report and the scratch axiom probe; the
submitted Lean proof and node records were already correct and were retained.
