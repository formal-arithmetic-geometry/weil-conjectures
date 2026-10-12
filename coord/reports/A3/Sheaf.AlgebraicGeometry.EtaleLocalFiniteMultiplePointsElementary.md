## What changed

Repaired the returned delivery by strengthening the private helper
`AlgebraicGeometry.transport_finite_open_piece`: its conclusion now also returns the
canonical equality `W = e.hom ''ᵁ V`. The proof supplies this equality by reflexivity,
and the induction call destructures the additional result. This removes the exact
word-for-word duplicate detected against `ElementaryLocalizeSplitPoints` while retaining
the existing proof of the target theorem and its signature.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.exists_etale_local_finite_multiple_points_elementary`.
No sorry remains in the delivered module and no holes were added. The proof still uses the
existing holed declarations `AlgebraicGeometry.exists_etale_finite_open_of_isolated_fiber_point`
and `AlgebraicGeometry.finitePiece_persistence_of_isIso_residueFieldMap`.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FibreProductPointResidueField`.
Removed old proof dependencies `lem-weil-pbc-fibre-product-points` and
`lem-weil-pbc-fibre-product-point-residue-field`: the canonical field-spectrum lift
proves the necessary existence and residue-field property without either statement.
The replacement dependencies are the existing Mathlib leaves
`lem-weil-pbc-morphism-from-spec-field` and
`lem-weil-pbc-residue-field-point-naturality`.
All other old proof dependencies are retained. This removes a direct import only:
`FibreProductPointResidueField` remains reachable through the one-point and persistence
modules, so this delivery does not claim that it prunes that module from the target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private helper with exactly the same statement as a
private helper in `ElementaryLocalizeSplitPoints`; the landing check rejects that duplicate
even though the latter module imports this one. The helper is now strictly stronger by
returning the image-open equality, which is true by its construction and compiles.

## New nodes

None.

## Forced adaptations

None. No module outside this sandbox was adapted.

## Second reading by A3

1. PASS: compared the delivered module and node with the repository using `diff`.
   The sole existing declaration, `AlgebraicGeometry.exists_etale_local_finite_multiple_points_elementary`,
   has a byte-for-byte identical signature (checked independently by textual comparison).
   No definition, public instance, public import, or target statement changed. The three
   new helpers are private proved theorems; the transport helper's image-open equality
   follows by reflexivity and does not change an existing interface.
2. PASS: the delivered file compiles without errors or warnings through `lcompile.py`.
   A scratch copy with `#print axioms` for all four declarations confirms that the three
   helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the main theorem also
   uses `sorryAx` through the existing one-point and persistence dependencies. No direct
   `sorry`, forbidden axiom/implementation construct, or holed definition is introduced.
   All existential witnesses are used inside theorem proofs, not to define arbitrary data.
3. PASS: no new split-off statement, hole, or node. Reviewed the private helpers:
   the section-from-field argument makes the reverse field map injective and split
   surjective; the canonical pullback lift has both required projections; `isoImage`
   transports the open and its distinguished point. The induction handles `n = 0`,
   singleton families, and repeated points without adding a distinctness hypothesis.
   Independent LeanFinder and Loogle searches with section/residue-field phrasing,
   together with `rg` in Mathlib, upstream and Sheaf, found the Mathlib factorization
   and naturality lemmas already used, rather than a shorter matching theorem.
4. PASS: the proof follows the induction, one-point localization, pullback pasting,
   and persistence route of [Stacks 02LL](https://stacks.math.columbia.edu/tag/02LL),
   checked against its statement and proof and [02LK](https://stacks.math.columbia.edu/tag/02LK).
   `dag/units/sk-thm-p1.json` was read: this item realizes neither the unit statement
   nor a numbered unit step, and its `realized` route is unchanged. Each retained
   import supplies signature vocabulary or a theorem actually used; all three
   Sheaf imports are proof-only. The unused direct import and both removed old
   proof-dependency nodes are now fully listed above. No global module pruning claimed.
5. PASS: the node's updated step 2 records the canonical lift and split-field argument;
   the remaining steps describe the Lean induction, transport and persistence. The
   `proof_deps` are exactly the union of the step `uses` lists, and `proof_origin`
   records the source and the agent's alternative point construction. The node's
   statement and Lean signature are unchanged; there are no new-node fields to check.

Second-reading changes: corrected `## No longer needed` to name both removed DAG
proof dependencies and distinguish direct-import removal from global module pruning.
The Lean proof and node were retained after review. One local hole closed, zero holes
added, zero split off; the theorem is conditional on the two existing open dependencies.
