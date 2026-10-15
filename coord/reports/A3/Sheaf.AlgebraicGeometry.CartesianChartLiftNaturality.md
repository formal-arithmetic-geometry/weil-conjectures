## What changed

Completed `AlgebraicGeometry.Etale.cartesianChartCohomologyLift_naturality` with the original
signature and the original raw-evaluation/adjunction/composition argument. The chart arrow's
projection equations follow from pullback uniqueness and `Over.w`; raw-class naturality,
shift-compatible pullback composition and adjunct exchange then give the stated equality.

`CartesianChartClassPullback` now constructs the same class through the real, irreducible
`cartesianChartClassPullbackCore`. The composition calculation in the item retains that named
construction while transporting map equalities and unfolds it afterwards. No proof was moved
out of the item to meet the time limit. The lift uses the existing canonical inverse class
`rawRestrictedCohomologyClass`. Added and proved `cartesianChartClassPullback_zero` in its own
`CartesianChartClassPullbackZero` module as the zero API.
The zero API is used by the vanishing caller. All existing public signature tokens are
unchanged; `chartExchange_finish` has only the line-wrapping change explicitly declared in
the change record.

Five dependent modules receive the necessary proof changes listed below. Every adapted module
was unclaimed when checked. The change record is
`coord/changes/A3-cartesian-chart-pullback-core.md`; it contains the complete downstream table
and verbatim old/new constructions. The new construction unfolds to the original four factors;
the raw class unfolds to the original inverse evaluation, so no mathematical definition changes.
Target statement review is reopened for users of the modified definitions, as the brief requires.

The first reader validation of the complete item compiled in 54.4 seconds against its changed
dependency, with all seven original submitted modules compiling cleanly. Validation also
checks the delivered set together and the unchanged textual callers separately; the delivery dry
run supplies the final compilation and axiom checks. No library-wide build was run.

## Proved and sorry left

Completed the assigned declaration:
`AlgebraicGeometry.Etale.cartesianChartCohomologyLift_naturality`
(node `lem-sc-cartesian-chart-lift-naturality`). One assigned obligation proved, zero new holes,
zero split-offs. There are no `sorry`s in any delivered Lean file.

The checkout supplied to the second reader already contains a textual attempted proof of this
declaration, with no literal `sorry`; the first worker's recorded compile of that version times
out at 60 seconds. Thus this is also a compilation repair. Relative to that checkout, the literal
holes closed and added are both zero. The earlier report's claim of one literal hole closed was
not supported by that comparison and is withdrawn. No ledger-net or whole-module-pruning gain
is claimed; the pinned sorry ledger, rather than the landing, decides those figures.

Also proved `AlgebraicGeometry.Etale.cartesianChartClassPullback_zero`
(node `lem-sc-cartesian-chart-class-pullback-zero`) and all private categorical helpers.
The new core is an explicit composite, with no data chosen from an unproved existence theorem.
The proof still uses the library's existing comparison and adjunction declarations; their
upstream obligations remain with their existing nodes.

## No longer needed

Removed the direct proof import of
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison`; it remains available through the
adjunction-comparison module used by this proof. Replaced the direct import of
`RawRestrictedCohomologyComparisonNaturality` and the duplicate private inverse-naturality proof
with the already proved `RawRestrictedCohomologyClass` naturality API. The item receives it
through the class-pullback module; the redundant direct import was removed in the second reading.

The item does not use the direct imports `CartesianChartExchangeMapNaturality`,
`CartesianChartExchangeConclusion`, `CartesianChartExchangeFinal` or
`CartesianChartExchangeObjects` that appear in the checkout's earlier candidate proof. It uses
`CartesianChartExchangeMapBridge` instead. The source-composition and shift helpers still need
`AbelianRawPullbackComposition` and `AbelianDerivedDirectImageTransitionShift`.
No whole module or existing node is claimed pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The checkout has no DAG record for the blueprint id
`lem-sc-cartesian-chart-lift-naturality`, and no node with this item's `lean.module`, despite the
module docstring and the brief referring to it. Added that missing record with the exact theorem
signature and the proof actually written. The existing chart-definition docstring ids
`def-sc-cartesian-chart-class-pullback` and `def-sc-cartesian-chart-cohomology-lift` also have no
records in this checkout; their declarations and mathematical meanings are preserved.
The new core has its own complete definition node; the proved zero API has its own statement
node and new module.

The unit `sk-thm-vanishing` has empty `realized.statement` and `realized.steps` entries. This
delivery changes none of them and follows the module's specified route. The only implementation
obstacle was repeated expansion of the derived pullback term during equality transport; keeping
its actual construction named resolved that obstacle without changing the degree range or adding
geometric assumptions.

## Forced adaptations

`Sheaf.AlgebraicGeometry.CartesianChartExchangeFinal` (unclaimed): the original proof at line 34
reported “Type mismatch: After simplification”: the expanded expression in its hypothesis did
not match `cartesianChartClassPullbackCore` in the goal. Unfold the core after the existing chart
pullback unfolding. The lemma's statement and visibility are identical.

`Sheaf.AlgebraicGeometry.CartesianChartExchangeFinish` (unclaimed): the original rewrite at
line 86 could not find `(asIso ...).inv x` after unfolding the lift, because the lift now uses
`rawRestrictedCohomologyClass`. Its `hzinv` now identifies that canonical class with the given
class by applying evaluation injectivity and `rawRestrictedCohomologyClass_spec`. The existing
finish calculation then applies unchanged. Replaced the `letI` proof binding by `let` to remove
its style warning, and wrapped the original overlong lines. No signature-token changes.

`Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality` (unclaimed): the original final term
at line 125 had the inverse-expanded source, whereas the goal now has the cached class. Remove
the now unnecessary inverse conversion and its congruences; use `hm.trans hR.symm` directly.
No other argument or signature changes.

`Sheaf.AlgebraicGeometry.CartesianRawClassChartData` (unclaimed): the original `change` at
line 117 failed because it expected an expanded inverse evaluation. Unfold the canonical raw
class where the lift is already unfolded. Include the new core in the private postcomposition
calculation's explicit simplification. All signatures and visibility stay identical.

`Sheaf.AlgebraicGeometry.CartesianHigherImageSingleRawClassVanishing` (unclaimed): the original
final simplification expanded the lift and chart pullback directly, leaving the new cached raw
class and core. Expand the raw class at zero and use the proved chart-pullback zero API, imported proof-only
from its own new module. This
preserves the exact zero conclusion and avoids repeating the derived construction.

## New nodes

`def-sc-cartesian-chart-class-pullback-core`: records the explicit four-factor inverse-image
construction and its use after free-source transport. It introduces
no proof hole. Edge cases: arbitrary integer shifts (including negative and zero) and empty
schemes use the same concrete composite; the construction is meaningful without a nonemptiness hypothesis.

`lem-sc-cartesian-chart-lift-naturality`: supplies the missing record for the existing item,
with its exact original statement, source, searches and the raw-class/shift/adjunction proof.
It introduces no Lean declaration or proof hole beyond the pre-existing item being proved.
The change record is `coord/changes/A3-cartesian-chart-pullback-core.md`.

`lem-sc-cartesian-chart-class-pullback-zero`: the same proved zero API, moved by the second
reader into its own new module as the brief requires. It is not a split-off obligation: its
proof is complete. Independent leanfinder, loogle and grep searches found generic zero-map
facts, which its proof applies directly. Empty schemes and negative, zero and positive integer
shifts are covered by the same additive-functor calculation.

## Second reading by A3

1. Compared all seven existing modules with the checkout using `diff`, and compared their
   declarations with the signature reader. Verdict: the assigned theorem and every existing
   public signature have identical tokens and types. All are byte-for-byte unchanged except
   the three line wraps in `chartExchange_finish`, explicitly declared in
   `coord/changes/A3-cartesian-chart-pullback-core.md`. Two private composition helper statements
   now use the concrete core instead of its expanded factors; this is also declared there.
   Unfolding the core gives the original four factors. Unfolding the canonical raw class gives
   the same uniquely determined inverse evaluation as before. No target text or mathematical
   definition has been weakened. All five original caller files fail against the changed
   dependencies at the reported lines; their adapted versions compile. Verdict: adaptations
   are necessary and preserve their interfaces.

2. Compiled the final eight-file set with `lcompile.py --all`: every file is clean, in
   6.6–53.5 seconds (the item: 51.0 seconds). Scanned all delivered code for holes and forbidden
   declarations: none. A scratch module prints the axioms of all ten public declarations.
   The item, core, zero API, both chart definitions, postcomposition, finish and exchange use
   only `propext`, `Classical.choice`, `Quot.sound`. The two adapted existence theorems retain
   `sorryAx` from already open imported results; their own proofs have no holes. The delivery
   tool additionally probes every added constant, including private helpers. Verdict: valid
   Lean proofs with no new axiom or hole, and no data chosen from arbitrary existence.

3. No statements are split off with `sorry`. The new zero theorem is the direct two-line
   consequence of additivity and zero composition; it works for negative and zero shifts,
   empty schemes, and zero objects without extra hypotheses. Moved it into its own new module
   and gave it its own node, as the brief requires. Independent searches used the distinct
   additive-functor/zero-morphism wording with leanfinder, loogle and grep; local source search
   found no existing specialized zero API. Verdict: true, needed by the zero caller, proved
   completely, and not a restatement of the item.

4. Read the target-down proof: the specified restricted transition becomes the raw affine
   map; the existing canonical-class naturality theorem transports its class; source and
   shift coherence compose pullbacks; existing chart adjunction exchange gives the result.
   The generic helpers express those elementary compositions without a new mathematical
   obligation. The item already reuses these shortest relevant library APIs. Removed its
   redundant direct raw-class import, which is supplied by the class definition module.
   All other remaining proof imports supply used declarations. The old item has no node, so
   there is no old `proof_deps` list omitted from `No longer needed`; removed direct imports
   are all listed, with no claim of whole-module pruning. Read `sk-thm-vanishing` and its
   empty `realized` lists; no unit statement or step is bypassed or changed. Verdict: route
   preserved and imports pruned to those needed by this proof.

5. Checked every new node's Lean signature against its actual declaration, dependency
   existence, and equality of `proof_deps` with the union of step uses. Updated the main
   node to cite the existing canonical-raw-class node and the chart-adjunction calculation
   node, rather than merely their broad prerequisites. The concrete core and zero API now
   have separate, accurate records, each with its actual module, source, complete proof,
   searches, unit and creation fields. Verdict: DAG and Lean agree.

Changes made by the second reading: separated the proved zero API into
`CartesianChartClassPullbackZero` and added its node and proof-only caller import; removed
one redundant import from the item; corrected the main node's proof dependencies; declared
signature whitespace and private-helper changes explicitly; corrected the report's unsupported
literal-hole progress claim; updated the change record's displayed construction and module
list. No mathematical proof argument or existing public statement was changed.

The first final dry run passed compilation and axiom probes but refused the new zero node's
search metadata: its validator requires LeanSearch separately from the Loogle/LeanFinder
category. Ran the additional LeanSearch query; the service returned Internal Server Error,
recorded truthfully as unavailable. The successful independent leanfinder, loogle and grep
searches and complete Lean proof are unchanged. Added this required search-attempt record.
