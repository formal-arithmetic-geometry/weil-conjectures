## What changed

Repaired `lean/Sheaf/CategoryTheory/SiteCoveringsCommonRefinement.lean` by proving both
common-refinement theorems from Mathlib's `ZeroHypercover.inter`,
`PreZeroHypercover.interFst`, `PreZeroHypercover.interSnd`, and
`IsPullback.isoPullback`. The supplied arbitrary pullback family is transported to the
canonical intersection by an isomorphism. The finite theorem uses
`Finite.induction_empty_option`, intersecting at the option step and composing the
inductive refinement morphisms. The unused proof-only import of
`Sheaf.CategoryTheory.SiteCoveringAxioms` was removed.

## Proved and sorry left

The declarations `CategoryTheory.Precoverage.siteCoverings_common_refinement` and
`CategoryTheory.Precoverage.siteCoverings_finite_common_refinement` are proved. No
`sorry` remains in the delivered module, and no new holes were added.

Holes closed: the two declarations above (2 of 2). Holes added: none (0).
This is a proof, not a decomposition; no statements were split off.

## No longer needed

The proof no longer needs the `Sheaf.CategoryTheory.SiteCoveringAxioms` import or the
DAG proof dependencies `def-weil-pbc-sites-and-cohomology` and
`def-weil-pbc-site-plus-construction`; all required constructions and axioms come from
Mathlib's `CategoryTheory.Sites.Hypercover.Zero`.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan rebuilt the covering by site axioms and did not exploit Mathlib's
canonical `ZeroHypercover.inter`. The upstream review correctly required transporting an
arbitrary `IsPullback` family along `IsPullback.isoPullback`; this is now implemented.


## Second reading by B3

1. **Visible interfaces — pass.** Read the complete repository/sandbox diff for
   `lean/Sheaf/CategoryTheory/SiteCoveringsCommonRefinement.lean`. Both existing
   theorem signatures are byte for byte identical, including all universes,
   hypotheses, the arbitrary `W`, `q`, `p`, and `IsPullback` family, the exact two
   projection index maps and `HEq` conclusions, and the finite-family conclusion.
   No declaration or definition was added or changed. The sole import removal is
   the proof-only `Sheaf.CategoryTheory.SiteCoveringAxioms`; no change record is
   needed.
2. **Proof and axioms — pass.** Compiled the file and the whole sandbox with
   `lcompile.py`, with no errors or warnings. Also compiled a scratch copy with
   `#print axioms` for each theorem: both use exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No `sorry` or forbidden declaration occurs
   in the delivered Lean code; no data is chosen from an unproved existence theorem.
   In the binary proof, flipping each supplied square makes `q` the first
   projection, so `isoPullback_hom_fst` proves the required structure-map equation.
   `mem_iff_of_iso` then transports membership in the correct direction. The first
   refinement triangle is definitional; the second is exactly `(h ij).w`.
3. **Split statements — pass, none.** No new statements, nodes, or holes were
   introduced. Checked empty covering index types: the product-index construction
   and componentwise isomorphism require no nonempty indices. Checked finite
   families of size zero, one, and two: the identity cover supplies the empty
   case, the option step refines the new member by `interSnd`, and the old members
   by `interFst` followed by their inductive morphisms. Equivalence transport also
   handles arbitrary finite index types and universes.
4. **Shortest route, pruning, unit — pass.** Read Mathlib
   `CategoryTheory/Sites/Hypercover/Zero.lean`: `inter` is the binary construction
   already provided; its definition pulls back then composes covers, as in
   [Stacks Tag 00W6](https://stacks.math.columbia.edu/tag/00W6), whose statement and
   proof were read independently. The arbitrary supplied pullbacks still require
   the explicit isomorphism, so using `inter` alone would not prove this signature.
   Searched the hypercover file for finite/common refinements and ran the logged
   `msearch.py ... grep 'ZeroHypercover.*(finite|common)|common.*refinement'`
   query (0 hits). No shorter finite-family lemma was found. The remaining public
   Mathlib import is needed by the signatures; the removed proof import is unused.
   `## No longer needed` lists both old DAG proof dependencies and the one removed
   import. Read `dag/units/sk-thm-p1.json` and its `realized` entries: neither removed
   dependency realizes a unit statement or step; this node is below the unit level.
   No unit route is bypassed. No claim is made that the removed module is globally
   unreachable from other targets.
5. **DAG agreement — pass after metadata repair.** Compared the entire node with
   the repository version. Only stage-3-owned fields differ: `proof` and
   `proof_deps` give the two actual constructions and have no project-node uses,
   since the implementations depend directly on Mathlib. Updated the previously
   stale `proof_origin` to name that implementation and its precise declarations
   and source locations while retaining the Stacks source. The node's statement,
   statement dependencies, Lean declarations, chapter, and unit are unchanged.
   There are no new nodes requiring additional fields or searches.

Second-reading changes: corrected `proof_origin` and made the closed/added-hole
counts explicit in this report; appended this review. No Lean proof changes were
needed.
