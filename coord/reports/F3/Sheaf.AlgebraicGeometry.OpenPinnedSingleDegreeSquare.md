## What changed
Reduced `AlgebraicGeometry.open_pinned_single_degree_square` from arbitrary integer degree to a degree-zero geometric square and shift covariance of the pinned base-change composite. The target statement and `pinnedSingleDegreeTensorComparison` definition are unchanged. Three real helper definitions record the source, target and composite, using the same composition-pinned derived counit; no object is chosen from arbitrary existence.

The proof shifts the degree-zero square, applies the shift covariance theorem once after global open restriction and once locally, whiskers the local comparisons by module restriction, and conjugates the shifted comparison isomorphisms. A proved private categorical lemma combines the three component equations by cancellation.

## Proved and sorry left
Closed: `AlgebraicGeometry.open_pinned_single_degree_square` (lem-pc-open-pinned-single-degree-square), by decomposition.
Added holes: `AlgebraicGeometry.open_pinned_single_degree_zero_square` (lem-pc-open-pinned-single-degree-zero-square) and `AlgebraicGeometry.pinned_single_base_change_shift` (lem-pc-pinned-single-base-change-shift). Each has a separate module and complete proof in words. No sorry remains in the target module. This is a decomposition, not a net reduction of holes: one closed, two added, net -1.

## No longer needed
Removed direct proof imports `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`, `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`, `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`, and `Sheaf.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes` from the target module. They remain dependencies of the degree-zero geometric statement; therefore none of their nodes or modules is claimed globally pruned. No unit statement or proof step is bypassed.

The target no longer directly uses these old `proof_deps` nodes (all are retained
in the new lemmas' plans or statement dependencies):
`def-pc-derived-base-change-map`, `def-pc-derived-open-restriction-maps`,
`def-pc-fibre-product`, `lem-pc-derived-pullback-open-restriction-universes`,
`lem-pc-restrict-derived-direct-image-open`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-sc-derived-open-restriction-adjunction-exact`,
`lem-weil-pbc-module-square-restriction-commutes`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction`.
No node or module is globally pruned. The second reader also removed the redundant
private composition import in the new shift module; that dependency remains
available through its public `SchemeDerivedBaseChangeMap` import.

## Where the brief, the DAG or earlier work was wrong
No original statement error identified. An exploratory split into arbitrary comparison isomorphisms was discarded because existence of the functor isomorphisms alone does not justify compatibility of arbitrary choices. The delivered route fixes this by transporting a commuting degree-zero square and each complete base-change composite along shifts. Shift covariance does not assert compatibility with arbitrary comparison isomorphisms.

Edge cases: degree zero gives identity shift; every negative or positive integer uses a shift equivalence. Zero modules and empty opens are retained in the degree-zero statement; shifting or whiskering those comparisons adds no nonemptiness, boundedness, flatness or properness assumption. The shift lemma requires only a commutative scheme square, independently of cartesianness or open restriction.

## New nodes
`lem-pc-open-pinned-single-degree-zero-square`: the geometric square only in degree zero, in `lean/Sheaf/AlgebraicGeometry/OpenPinnedSingleDegreeZeroSquare.lean`. Its proof follows the original geometric plan with the integer-degree generalization removed.

`lem-pc-pinned-single-base-change-shift`: shift covariance of a single base-change composite, with no open restriction square and no cartesianness assumption, in `lean/Sheaf/AlgebraicGeometry/PinnedSingleBaseChangeShift.lean`. Applied to both the global and restricted schemes; the target proof performs the combination. Source, target and composite helper definitions in this module are explicit functor/morphism constructions. No change record is needed: existing statements and definitions are unchanged.

## Second reading by F3
1. Compared the target module against the repository with `diff` and the declaration
   parser. Verdict: both existing signatures and the complete body of
   `pinnedSingleDegreeTensorComparison` are byte-for-byte unchanged; no public import
   changes, extra hypotheses, weakened conclusions or altered existing definitions.
2. Read all three modules and the categorical cancellation proof. The only new holes
   are the two named public theorems reported above; all three helper definitions are
   explicit constructions. Their counit comes from the already proved composition
   theorem, not from an unproved mere-existence assertion. Compilation and axiom
   verification are recorded below after the delivery checks.
3. Checked the two statements independently against Stacks 08HY (the mate), 08FE and
   0D5U (restriction of K-injectives and derived direct image), and the single-functor
   shift construction. Degree zero removes precisely the integer-shift part of the
   geometry; shift covariance has no open or cartesian hypothesis and is a separate
   part of the argument. Neither restates the full item. Empty opens, zero modules,
   identity squares, n=0 and negative degrees introduce no missing hypothesis.
   Repeated leanfinder, loogle and grep searches using localization counits,
   translation and NatTrans.CommShift rather than the author's queries. The hits
   provide constituent identities, not either complete statement; repository searches
   likewise found no usable duplicate or shortcut. No split hole could be closed
   immediately with these results.
4. The proof applies the shift functor to the zero-degree equation and combines the
   two independent covariance equations by cancellation; this is a real reduction.
   The four removed geometric imports and their old dependency nodes remain needed
   by the degree-zero lemma, so no global pruning is claimed. The unit record
   `sk-thm-picard-f-representable.json` has empty realized lists; this reduction
   changes none of its statement or step realizations and retains the geometric route.
5. Read each delivered node alongside its Lean declaration. The target's two proof
   dependencies are exactly the two new lemmas used. New nodes carry their source,
   self-contained statements, complete proof plans, creation and Lean records,
   searches and blueprint ancestry. Existing statement fields remain unchanged.

Changes by the second reader: removed the redundant private
`DerivedPullbackComposition` import from `PinnedSingleBaseChangeShift` (already
publicly imported by `SchemeDerivedBaseChangeMap`); corrected the new helper
docstring's claim of a unique counit to composition-pinned counit and explained that
shift comparisons are transported using the selected counits' universal properties,
rather than assuming an arbitrary selected counit respects a pre-existing shift
structure; corrected “degree-n” to “degree-zero” in the new zero-degree node's plan.
No theorem statement was changed. The final simplification was subsequently
replaced by `exact h`: Lean accepts the transport equation by definitional equality,
so expanding both composite definitions in a simp proof was unnecessary. This remains one closed hole and
two added holes, a decomposition with net -1, not a completed geometric proof.

Validation: `deliver3.py F3 Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare
--no-push` printed OK (dry-run commit fe2344ea9a); all three delivered files compiled
and the automated axiom probes and preflight passed. A separate import-only scratch
probe with `#print axioms` compiled successfully: the existing pinned comparison and
all three new definitions depend only on `propext`, `Classical.choice`, `Quot.sound`;
the target and the two split theorems additionally depend on `sorryAx`, as reported.
No other axioms occur. The target is proved relative to the two open lemmas, not
axiom-clean in the completed-target sense.

Performance repair: the first two final delivery attempts compiled the new modules
but timed out at the target's final simplification. Replacing its final `simpa only`
with `exact h` compiled successfully under the unchanged 60-second per-file limit
(the logged 138.6 seconds include waiting for a compiler slot). No definition,
signature, dependency or hole changed. The final delivery checks below validate
this smaller proof term again.
