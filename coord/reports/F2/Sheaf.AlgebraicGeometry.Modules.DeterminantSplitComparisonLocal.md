## What changed

Verified both existing proofs and made their final steps explicit:
`determinant_split_comparison_local` now uses `exact hd` rather than `simpa`, since
`LinearEquiv.ofBijective` has the original linear map as its forward function.
`determinant_split_comparison_restriction` rewrites both occurrences with `hd` and
then applies `hn` directly. No signature, visibility, definition, or import changed.
The module compiled cleanly before and after these changes through lcompile.py.

The queued upstream review #1428 repair has already landed. Its current interface
requires a natural linear family `dNatural`, its naturality `hn`, and pointwise
equality `hd` with the equivalences. The caller in DeterminantSplitComparison
supplies precisely the natural family from determinant_split_linear_maps_exists,
its naturality, and definitional equality after conversion to linear equivalences.
This delivery verifies that repaired state; it claims no new mathematical progress.

## Proved and sorry left

Holes closed: none. Holes added: none. The assignment's base module already contains
zero sorries. Both declarations retain complete proofs:

- AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local
  (new-determinant-split-local).
- AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction
  (new-determinant-split-restriction).

Every sorry left in the item or added elsewhere: none. No decomposition or new
module was required. The existing linear construction and local bijectivity
imports remain genuine proof dependencies; their signatures were checked.

## No longer needed

None. No import, node, or module was pruned. The local theorem still follows its
three DAG steps: construct linear maps, obtain a bijective neighborhood, convert
with LinearEquiv.ofBijective and retain the generator formula. The restriction
lemma follows its existing elementary substitution step. The unit route is kept.

## Where the brief, the DAG or earlier work was wrong

The brief says the module still contains sorry, but the supplied checkout has
complete proofs of both declarations, with E3 AUTO proof review records dated
2026-10-14. coord/repairs.txt still lists the earlier unconstrained-c statement
rejected by upstream review #1428. The current signature no longer has c and
already incorporates the naturality-family repair documented in the landed
change records. No repeat interface change or forced caller adaptation is needed.

The restriction proof uses no rank, nonempty-open, or nonzero-ring hypothesis;
it is valid on empty opens and at rank zero. The local proof uses exactly the
rank and splitting hypotheses of its two existing dependencies. No new statement
was introduced. Loogle found LinearEquiv.ofBijective and its application lemma;
local text search found the existing assembly in DeterminantSplitComparison.


## Second reading by F2

1. Unchanged interface: PASS. Read the whole sandbox module and diffed it against
   the repository module. Only `simpa using hd ...` to `exact hd ...` and the two
   explicit rewrite instances to `rw [hd, hd]` differ. Every existing signature,
   docstring, visibility command, definition and import is byte-for-byte unchanged.
   No target or other module is delivered or adapted.
2. Proof and trust: PASS. lcompile.py compiled the delivered file without errors or
   warnings (3.8 seconds). A scratch copy with `#print axioms` for both
   `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local` and
   `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`
   compiled (4.3 seconds); each lists exactly `propext`, `Classical.choice`,
   `Quot.sound`, with no `sorryAx`. No sorry, forbidden declaration, hollow
   definition or arbitrary witness chosen from an unproved existence occurs.
   The linear family comes from the unique natural-family theorem; conversion
   by `LinearEquiv.ofBijective` retains its original forward linear map.
3. Split statements: PASS, vacuous. No statement, helper, node or hole was added.
   Read the signatures of the existing linear-map existence and local-bijectivity
   dependencies: the first supplies the exact generator formula, and the second
   supplies bijectivity for precisely the composite subopen inclusion. The local
   theorem is vacuous for empty U; zero ranks and zero rings require no extra
   cancellation or nonempty hypothesis. Restriction is substitution for arbitrary
   ranks and opens, so these edge cases use the same proof.
4. Route and pruning: PASS for this delivery. Independent Loogle search for
   `LinearEquiv.ofBijective` returned the constructor and its application lemma;
   the latter is definitional, as confirmed by `exact hd`. Local text search and
   reading DeterminantSplitComparison found the existing assembly retaining the
   natural linear family; using it backwards here would introduce a dependency
   cycle. Both proof-only imports are used. The public imports supply the exterior
   sheaf, tensor-section notation, locally free rank, short complex and biproduct
   interfaces appearing in the signatures. No old proof dependency is unused,
   so `No longer needed: None` is complete. Read sk-thm-picard-rr.json: its current
   `realized.statement` is empty and `realized.steps` is `[[]]`; this is existing
   incomplete blueprint metadata, not a populated realization verified here.
   This delivery leaves the unit route and that metadata unchanged.
5. DAG agreement: PASS. Read both item nodes and both proof-dependency nodes.
   The local node's three steps are exactly linear construction, local
   bijectivity, and conversion preserving the formula; its two proof_deps are
   exactly the non-elementary declarations called. The restriction node has an
   elementary substitution step and empty proof_deps, matching the Lean proof.
   Both recorded Lean statements agree with the delivered signatures. The
   existing proof_origin records remain applicable. No node edits are needed.

Second-reading changes: corrected the report's prior-review group from G2 to E3,
added the precise qualification about the unit's empty realization fields, and
recorded the independent axiom audit. No additional Lean repairs were necessary.
The blueprint literature paths named in the nodes are absent on this machine;
this proof-only review uses the recorded unit text, unchanged node statements,
landed interface-change records, and the actual Lean dependency declarations.
Both declarations were already proved at the assignment baseline: 0 holes closed,
0 holes added, 0 split off; no new mathematical progress is claimed.
