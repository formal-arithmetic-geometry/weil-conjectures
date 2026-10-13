## What changed

Proved `AlgebraicGeometry.Scheme.picardRankMatch_ordinary_ranks` without changing its
signature. Added proof-only imports of `FiniteDescent`,
`FiniteLocallyFreeStalkFinrank`, and `PicardBaseChangeStalkFinrankEq`.

The proof obtains local frames from universal rank matching, proves finite local
freeness by open-cover descent, and identifies iterated and composite ordinary
images using the canonical fibre-product isomorphism. The identity witness supplies
a rank r for the source after every further pullback. The existing stalk-finrank
equality supplies rank r at the target stalks. A proved private helper reindexes
finite local frames using these stalk finranks and glues them into fixed rank r.
Restriction finrank is proved by germ compatibility and Mathlib's semilinear rank
invariance. All private helpers are proved; no new public declarations were added.

Updated the existing DAG node's proof, proof dependencies and proof origin to match
this argument. Single-file compilation succeeded without warnings in 18 seconds.
The new imports are private to the proof, and the existing public imports remain.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.picardRankMatch_ordinary_ranks`
(node `lem-sc-picard-rank-match-ordinary-ranks`). No sorry remains in the delivered
module. Holes added: none. Split-off statements: none.

The proof uses the existing unproved declaration
`AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finrank_eq`
(node `lem-sc-picard-base-change-stalk-finrank-eq`); its proof is the next item,
not part of this delivery. Thus this closes the upper proof relative to the named
planned dependency, and does not claim transitive axiom-freedom.

## No longer needed

Removed the redundant proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`: its declarations
remain available through the required `FiniteDescent` import.

No original public import removed: all serve the unchanged signature.
The direct proof no longer needs node `lem-sc-picard-fiber-rank-clopen` or module
`Sheaf.AlgebraicGeometry.PicardFiberRankClopen`. Its empty/nonempty fibre analysis
is already encapsulated by the existing stalk-finrank comparison, so the updated
node drops that direct dependency. This does not assert that the module is globally
unreachable. No other planned dependency is dropped.

The speculative auxiliary modules and nodes used during development were removed;
none is included in the delivery.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned separate empty-fibre decomposition is
unnecessary here because the existing stalk-finrank theorem handles it.
The original module had no proof-dependency imports; the needed ones were added.
The unit statement and its steps remain unchanged.

A first dry-run refreshed the clone while the new item was temporarily absent from
the server base. The original signature was retained in the sandbox; the item is
present again in the current base. No repository files were edited by hand.

## Second reading by T1

1. PASS: compared the only delivered module and node against the repository.
   The existing theorem signature is byte-for-byte identical, as is its docstring.
   No public definition, instance, attribute, option or import was changed; all
   new helpers are private. No interface change record is needed.
2. PASS: local single-file compilation succeeded without warnings. Text inspection
   found no sorry or forbidden declaration in the delivered module. A scratch copy
   with `#print axioms` for all six declarations showed only propext,
   Classical.choice and Quot.sound for the five private helpers; the public theorem
   additionally uses sorryAx through the existing named stalk-finrank dependency.
   The isomorphisms are constructed using adjunction uniqueness and explicit
   fibre-product associativity, not arbitrary witnesses of mere existence.
3. PASS: no statements were split off and no holes were added. The constant-rank
   helper starts with finite local freeness, so finite frame cardinalities really
   compute stalk finrank. Scheme local rings are nonzero. For r=0 the reindexing
   uses the empty frame; on an empty scheme the point-indexed cover is empty and
   the fixed-rank assertion is vacuous. Both alternatives for F are handled.
4. PASS after import cleanup: read the proof from the public theorem downward,
   checked its transports and local gluing, and searched the upstream modules,
   Sheaf, Mathlib scheme-module files and LeanFinder with the alternate query
   "finite locally free sheaf constant stalk finrank implies fixed rank".
   The hits concern algebraic rankAtStalk, not a shorter scheme-sheaf theorem.
   FiniteDescent publicly imports LocallyFreeRank, making the separate proof-only
   import redundant; removed it and recompiled. The original proof_deps differ
   only by the dropped lem-sc-picard-fiber-rank-clopen, already listed above.
   The unit sk-prop-av-cube is untouched, including its realized fields (currently
   empty); this reduction lies below the unit and bypasses none of its steps.
5. PASS: the node's three proof steps match local descent, iterated-image transport
   and stalk-finrank gluing in Lean. Its proof_deps are exactly the union of the
   steps' uses, and proof_origin accurately describes this reduction. The statement,
   source, stmt_deps and blueprint records are unchanged. There are no new nodes.

Second-reading change: removed the redundant private LocallyFreeRank import and
recorded the independent checks. No proof-body repair was necessary. One existing
hole closed, zero added; no claim of transitive axiom-freedom or global pruning.
