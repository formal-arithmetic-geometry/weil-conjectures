## What changed

`Sheaf.Paper.CondensedQbarBaseChangeCompatibility` now proves the proper pushforward
coefficient-change clauses by the existing imported instance
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`. Properness of the lower
edge follows from the chosen pullback identification and proper base-change stability. The
source and target comparisons are composites of isomorphisms. The final equality uses the
separate, strictly simpler `constructibleToQbar_exchange_equality`.

The second reader moved the four comparison definitions verbatim to the new data module
`Sheaf.Paper.CondensedQbarComparisons`, publicly imported by the item. This lets the new module
`Sheaf.Paper.CondensedQbarExchangeEquality` state the coherence equality without a dependency
cycle. No existing declaration signature, body of a definition, or target statement changes.
The new equality needs only a commutative square; it neither asserts isomorphy nor requires
properness. Its proof in words uses coherence of pull comparisons and mate pasting, with no
assumption of derived faithfulness of restriction of scalars.

Change record: `coord/changes/constructibleToQbarComparisons.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_baseChange_compatibility`, node
`prop-weil-pbc-qbar-condensed-basechange-compatibility`. Its proof now explicitly establishes
both push isomorphism clauses and both composite isomorphism clauses.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_exchange_equality`, node
`lem-weil-pbc-qbar-condensed-exchange-equality`, in
`Sheaf.Paper.CondensedQbarExchangeEquality`. It is the equality clause alone, with weaker
hypotheses, and is strictly part of the original conjunction. Its body is exactly `by sorry`.
No sorry remains in the item's module or in the moved data module. No definition contains
sorry. No new data are chosen from unproved existence statements.

This is a decomposition, not a completed proof: one original hole closed and one new hole
added, giving zero net hole reduction before any import-closure pruning. The existing proper
coefficient-change instance and other upstream preservation inputs remain open; this delivery
does not prove the all-unbounded claim of that instance.

All three modules compile without errors or warnings through `lcompile.py --all`. A scratch
copy printed axioms for all six relevant declarations: only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` occur. The scratch file was removed. The maintainer's global build
and pinned sorry ledger remain the authority for closure figures.

## No longer needed

Removed these eight direct proof imports from the item:

- `Mathlib.Topology.Algebra.Module.FiniteDimension`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts`
- `Sheaf.Paper.ProfinitePointPullback`

The chosen-Cartesian-square import stays public in the item, whose theorem statement needs it.
The other three old public imports are public imports of the data module and remain publicly
reachable from the item. The two proof imports of the item are the equality module and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`. Each public import of the data module supports
its stated objects or definitions. The equality module publicly imports the data it states.

Every old proof dependency absent from the new direct `proof_deps` is listed here:

- `lem-weil-pbc-finite-dimensional-linear-homeomorphism`
- `def-weil-finite-subextension-directed-set`
- `lem-weil-pbc-profinite-point-pullback`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-sheafification-exact`
- `def-weil-pbc-proetale-operations`
- `lem-weil-pbc-proetale-bounded-below-coproducts`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-weil-pbc-condensed-e-realization`
- `prop-weil-pbc-qbar-condensed-two-colimit`
- `pqf-lem-locnoeth-lft`

Some remain indirect dependencies of the data or the coherence proof plan, in particular the
point-pullback node. No module is withdrawn, and no module is claimed to be unreachable from
all targets. `dag/units/sk-thm-properbasechange.json` and all its `realized` fields are kept.
Properness stability is an existing Mathlib tool; the coefficient-interface decomposition
changes no step of the unit route.

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly said that no imports were removed: its file already removed
three, and second reading removed five further unused proof imports. Its new node had an
ellipsis instead of the Lean signature, lacked the required search kinds, depended back on
the parent theorem in `stmt_deps`, and carried the parent's blueprint tag in the sorry docstring.
These are repaired. Both new nodes have real recorded searches and verbatim parsed signatures.
LeanSearch was unavailable; LeanFinder, Loogle and source grep ran successfully. Generic mate
identities are useful tools, but no existing theorem directly states this derived condensed
coefficient exchange. The existing ringed tensor-exchange theorem concerns a different
coefficient presentation and does not supply the required comparison coherence without a bridge.

The proper-base-change node is the scheme-theoretic stability fact, not the proper
coefficient-change isomorphism. The main proof now explicitly identifies that imported
upstream instance and its still-open status. The original bounded-below basis argument is
not claimed as a proof of the instance's stronger all-unbounded statement.

The first equality explanation did not justify derived faithfulness of scalar restriction.
The revised explanation proves equality by mate pasting, so it does not need that assertion.
The remaining formal obligation includes verifying coherence of the *specified* derived pull
comparisons with composition; it is not just an invocation of ordinary naturality.

## New nodes

`def-weil-pbc-qbar-condensed-comparisons` records the four unchanged data constructions in their
new common module. It has no sorry and creates no alternative coefficient category or map.

`lem-weil-pbc-qbar-condensed-exchange-equality` records only the exchange equality for a
commutative square. Its three proof steps are the identification of the push comparison as
the mate of the inverse pull comparison, the coherent pullback cube, and mate pasting followed
by restriction to the full subcategories. It has its own module, exact Lean statement,
source, natural-language proof, and search records.

Change record: `coord/changes/constructibleToQbarComparisons.md`.

## Second reading by C1

1. Compared the delivered module with the repository and checked the parsed declarations.
   The original theorem signature is byte for byte unchanged. All four moved definitions
   have identical signatures, bodies and docstrings. No target or outside module was edited.
   The relocation and unchanged downstream meaning are declared in the change record.
2. Compiled all three files without errors or warnings. Checked all six declarations with
   `#print axioms`; only the three allowed axioms and existing/new `sorryAx` occur. Searched
   the delivered sources for forbidden escape declarations and data holes: none. Exactly one
   named theorem remains sorry, listed above with its matching node.
3. Read the equality from its definitions and the mate API. It asserts only the equality
   clause, without properness or Cartesianity, and is strictly simpler than the conjunction.
   For identity squares it is the unit/counit triangle calculation; for zero complexes both
   routes are zero; for arbitrary commutative squares the coherent pullback cube has the same
   types and its mates have the displayed orientation. Neither exchange is inverted. Repeated
   searches with different words using LeanFinder, Loogle, LeanSearch (unavailable) and grep;
   inspected the generic mate APIs and the ringed tensor-exchange result. No duplicate found.
4. Read from the original target down. The existing proper coefficient-change instance is
   the shortest available proof of the isomorphism clauses. Removed all eight unused direct
   proof imports, recorded every unused old direct node dependency, and preserved the unit's
   `realized` route. Existing public data remain available through the public data import.
5. Checked both new nodes and the changed main node against the Lean. Exact new signatures,
   docstring blueprint, statement dependencies, proof-step unions, sources and proof origins
   are consistent. The main node records the actual upstream instance and the new equality
   reduction, and the equality no longer depends on its parent statement. Existing mathematical
   node statements and all unit records are unchanged.

Second reading changed: warning-producing local instance syntax; removal of the unused chosen-square import from the
data module while keeping it public in the item; eight-import pruning and
its report; unchanged relocation of the four comparison definitions with a change record;
separate equality module with weaker square hypotheses and a mate-coherence proof explanation;
new data node; exact signatures, blueprint tag, search records and dependency metadata;
honest decomposition counts and the still-open upstream inputs.
