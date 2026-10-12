## What changed

Completed the reduction of `AlgebraicGeometry.gabber_h0_finite_lift` without changing its
signature. The proof constructs the finite-cover witness, proves injectivity of restriction
on the double fibre product, and cancels that restriction to establish the descent equation.
The terminal-object injectivity helper applies the existing public theorem
`gabber_h0_etale_injective` and transports it along the unique terminal-object
isomorphism using inverse-image unit naturality; it has no sorry. The duplicate private
`zarEtale` abbreviation and `zarEtale_continuous` theorem have been removed.

Added two intermediate modules, `Sheaf.AlgebraicGeometry.GabberH0FiniteSection` and
`Sheaf.AlgebraicGeometry.GabberH0ProjectionRestrictions`, with their nodes. They state
strictly separate parts of the original argument: construction of the section with its
closed-fibre equation, and equality of projection pullbacks after restriction. Neither
asserts the descent equation required by the item. Proof-only imports keep these additions
out of the item's public interface.

All three modules compile together in import order with lcompile. Their new statements
were checked against Stacks Tag 09ZF, lemma-gabber-h0, in the local source copy. The unit
sk-thm-iff retains its degree-zero comparison route. Empty schemes and identity immersions
are allowed; the projection-restriction calculation needs no geometric hypotheses.

## Proved and sorry left

Proved `AlgebraicGeometry.gabber_h0_finite_lift` (one original sorry removed),
and `unit_injective_terminal`. No sorry remains in the item's
module. This is a reduction to named intermediate statements, not an axiom-free completion
of its transitive dependencies.

The delivery adds exactly two sorries, each the whole proof of a public theorem:

- `AlgebraicGeometry.gabber_h0_finite_section`, node
  `lem-weil-pbc-gabber-h0-finite-section`, in `GabberH0FiniteSection.lean`.
- `AlgebraicGeometry.gabber_h0_projection_restrictions`, node
  `lem-weil-pbc-gabber-h0-projection-restrictions`, in `GabberH0ProjectionRestrictions.lean`.

Each has its source and complete proof in words in its docstring and DAG node.
Existing imported declarations are used with their present proof status.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Paper.GabberZariskiEtaleRestrictionInjective`.
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`.

These two direct imports are replaced by `Sheaf.AlgebraicGeometry.GabberH0EtaleInjective`,
whose public theorem is reused. Its node `lem-weil-pbc-gabber-h0-etale-injective` is again
a direct proof dependency. The two comparison modules remain transitive dependencies.

Other direct proof imports removed in the original reduction:

- `Sheaf.Paper.SiteSheafificationSectionsLocal`.
- `Sheaf.Topology.ClosedPushforwardConstantStalks`.
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement`.

The last three arguments remain in the finite-section intermediate's source proof; they
are not claimed to be globally pruned. The comparison module remains a transitive
dependency through the injectivity theorem.
All original local-representation, shrinking, cover and gluing dependencies are moved to
that intermediate's proof plan. Finite base change/composition and closed-immersion base
change remain used by instances in the main proof. Surjective base change is unnecessary
for this reduction. No other global pruning is claimed.

Complete list of old direct proof dependencies moved to the finite-section node:

- `lem-weil-pbc-closed-pushforward-constant-stalks`.
- `lem-weil-pbc-sets-inverse-image-stalk`.
- `lem-weil-pbc-sheaf-sections-determined-by-germs`.
- `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`.
- `lem-weil-pbc-etale-base-change-finite-limits`.
- `lem-weil-pbc-site-sheafification-sections-local`.
- `lem-weil-pbc-presheaf-pullback-sets-left-exact`.
- `lem-weil-pbc-filtered-colimit-sets-elementwise`.
- `lem-weil-pbc-etale-composition-cancellation`.
- `lem-weil-pbc-etale-morphism-open-map`.
- `def-weil-closed-immersion`.
- `def-weil-pbc-etale-site`.
- `def-weil-pbc-etale-sheaf-of-sets`.
- `lem-weil-pbc-etale-local-on-source`.
- `lemma-weil-pbc-finite-refinement-etale-cover`.
- `def-weil-pbc-topological-inverse-image`.

Old direct dependencies no longer used by either construction plan:

- `lem-weil-pbc-surjective-base-change`.
- `def-weil-finite-integral-morphism`.

The comparison-injectivity node is now only transitive for the item, and also occurs
in the finite-section gluing step. The inclusion-morphism-of-sites node is likewise
transitive rather than direct for the item. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox retained compiled artifacts for the finite-section and projection
lemmas but contained neither their source modules nor their nodes. They were not existing
library statements, contrary to the earlier report. This made local compilation succeed
and server compilation fail. Both source modules and nodes are now included in the delivery.
The earlier report also contained a second-reading section; it has been removed for the
independent second reader to write. The returned version duplicated a private continuity
theorem already in
`GabberH0EtaleInjective`, and the landing import-pruning check correctly refused it.
The repaired helper now actually applies `gabber_h0_etale_injective`; its compiled
module is available. Both duplicate private declarations are removed, the two direct
comparison imports are replaced by the injectivity import, and the main node records
that route. The stale second-reading section was removed for a fresh independent review.

## New nodes

`lem-weil-pbc-gabber-h0-finite-section`: Tag 09ZF's local representative, finite refinement,
and Zariski gluing construction, stopping before the double-projection equation. Its
statement preserves the item's hypotheses and only asks for the closed-fibre equation.

`lem-weil-pbc-gabber-h0-projection-restrictions`: Tag 09ZF's pullback compatibility
calculation on the double closed fibre. It is independent of finiteness and injectivity;
the main theorem supplies injectivity and cancels the restricted equality. Three real
Mathlib searches are recorded for each node; LeanSearch returned a service error, and
LeanFinder and grep supplied no matching theorem. No change record is needed: existing
public statements and definitions are unchanged.

## Second reading by B2

1. Compared the item with the repository by diff and extracted its complete theorem
   signature: it is byte for byte identical. No existing public declaration or
   definition changes. The existing node changes only proof, proof_deps and proof_origin.
2. Compiled all three modules in import order with lcompile. Scratch copies with
   #print axioms for the item, its private terminal helper, and both new theorems
   show only propext, Classical.choice, Quot.sound and sorryAx. The item and helper
   contain no sorry; exactly the two reported public intermediate theorems have
   whole-proof sorries. No forbidden declaration or hollow definition was found.
3. Read both new statements, their docstrings and their nodes. Checked against
   [Stacks Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF), including the
   shrinking step needed before gluing. The finite-section conclusion omits the
   descent equation; the projection lemma proves only equality after restriction
   and needs no geometric hypotheses. Neither restates the item. Empty schemes,
   identity immersions and identity covers cause no exception; if Z is empty and
   X nonempty, hZar is contradicted by the two-element constant sheaf.
   New Lean signatures match their node records after whitespace normalization.
   Independent LeanFinder searches for extension by Zariski gluing and cartesian
   square compatibility returned ordinary gluing/topological pullback lemmas,
   with no matching finite lift or etale projection statement. Mathlib grep and
   repository/upstream searches found no existing replacement. The composition
   theorem supplies the machinery, rather than either new conclusion.
4. Checked the reduction from the top down: finite section, restriction equality,
   finite double-product injectivity, then cancellation. The helper reuses
   gabber_h0_etale_injective and transports along a terminal isomorphism.
   Compared all old proof_deps with the new list and the pruning report; every
   removed dependency is accounted for, including those moved to the construction
   plan. sk-thm-iff realized and its degree-zero comparison route are retained.
   No quick proof of either remaining construction/transport lemma was found.
5. Checked proof steps, proof_deps unions, proof_origin, source, chapter, unit,
   split status, created/blueprint records, searches and Lean records of both
   new nodes. They agree with the actual reduction and the documented remaining
   arguments. No new axiom or changed meaning is hidden in the definitions used.

The second reading changes the report only. A narrower import of the module
containing the descent definitions was tested, but that newly split module has
no compiled artifact in the last green build available locally. The working
imports are therefore retained, as the project contract requires. No Lean proof,
statement, definition, node or public import changes were necessary.
