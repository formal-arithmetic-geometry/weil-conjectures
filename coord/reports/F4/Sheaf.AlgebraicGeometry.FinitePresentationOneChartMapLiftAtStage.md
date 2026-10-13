## What changed

Replaced the saved identical-statement `FinitePresentationOneChartMapLiftCore` attempt with two distinct parts of the argument: ordinary affine chart Hom descent, and canonical transport of an already supplied ordinary lift along a general scheme triangle. The item's signature and public imports are unchanged. A new real, irreducible predicate `AlgebraicGeometry.chartOrdinaryMapRecovery` packages the ordinary recovery equation. Repeated unfolding of its adjunction-based comparisons caused the saved slow compile; the explicit predicate and local irreducibility of the tensor comparisons remove that cost. Its proof restricts the original modules to the selected chart, supplies their finite-presentation and quasi-coherence instances, conjugates the limit map, obtains a stage map, and explicitly conjugates that map to the required restriction of tensor pullback.

## Proved and sorry left

The hole in `AlgebraicGeometry.finitePresentation_one_chart_map_lift_at_stage` is reduced to two strictly simpler named theorems. This is a decomposition, not a completed mathematical proof; one original hole is closed and two lower holes are added (net -1).

The remaining holes added by this delivery are:

- `AlgebraicGeometry.affine_chart_ordinary_map_descent` (`lem-pc-affine-chart-ordinary-map-descent`): finitely presented modules live directly on the affine chart; the ambient sheaves and all tensor-versus-restriction comparisons are absent.
- `AlgebraicGeometry.chart_tensor_pullback_lift_transport` (`lem-pc-chart-tensor-pullback-lift-transport`): an identity for an arbitrary scheme triangle and a supplied ordinary lift. There are no directedness, limit, affinity, finite-presentation or quasi-coherence assumptions, and this statement constructs no finite-stage lift.

The item's module contains no remaining `sorry`. The additional definition `AlgebraicGeometry.chartOrdinaryMapRecovery` has no hole; it is the explicit comparison equation. No data definition has been added, and no data is selected from an unproved existence theorem to define an object. The witnesses of the descent theorem are used only inside the proof of the existential target.

## No longer needed

The new recovery-definition module imports only `Mathlib.AlgebraicGeometry.Modules.Sheaf`; its redundant `Sheaf.AlgebraicGeometry.BaseChangeConventions` import was removed. Removed the item's direct proof import `Sheaf.Algebra.FinitePresentationColimit`; the algebraic descent remains needed by the ordinary affine descent node and is its proof dependency. The original proof-dependency nodes `def-pc-fibre-product`, `def-pc-tensor-pullback-composition-iso`, `def-pc-open-cover-tensor-pullback-comparison`, and `lem-pc-fp-module-map-descent-affine` remain needed below the two parts or in the public signatures: no existing library node or module is claimed globally pruned.

The saved uncommitted `FinitePresentationOneChartMapLiftCore` module and `lem-pc-fp-one-chart-map-lift-core` node are omitted entirely: they just repeated the item. The saved claim of an upper-tail reflexivity lemma being pruned is unsupported by files in the current attempt and is not counted. No other existing module is changed or adapted.

## Where the brief, the DAG or earlier work was wrong

The previous core statement had exactly the original hypotheses and conclusion, so destructuring and reassembling its witnesses did not constitute a reduction. Its node also copied an unrelated Lie algebra source, statement dependencies and blueprint identity, and its Lean signature was an ellipsis. These were substantive defects, not a tool failure. This attempt replaces that core rather than merely repairing its metadata. Both new nodes have actual sources, full statements, verbatim Lean signatures and the three required search kinds. Updated both recorded signatures after introducing the explicit recovery predicate. LeanSearch was unavailable with an Internal Server Error, which is recorded without inventing search results.

The unit `sk-thm-picard-semicon` has no realized node for this item; its statement and route are unchanged. Edge cases checked for the new statements include empty affine charts, zero modules, identity maps and equivalent indices of a preorder. The upper tail is nonempty because it contains j. Neither lemma requires a finite cover, Noetherian base or quasi-compact ambient scheme.

## New nodes

`lem-pc-affine-chart-ordinary-map-descent` is the ordinary affine Hom descent part of the original node's first step and algebraic descent step, following Stacks Tags 01ZR and 05N7 (2). It retains the existing algebraic finite-presentation descent dependency.

`lem-pc-chart-tensor-pullback-lift-transport` is the comparison part of the original node's second step, following Tags 0095 and 0096 and the existing categorical associativity tool. It is independent of affine geometry and finiteness. Existing signatures and visibility are unchanged. The conservative preflight nevertheless requires a record for the local attribute command; see `coord/changes/one-chart-lift-local-transparency.md`. No existing user is adapted.

`def-pc-chart-ordinary-map-recovery` records a fully constructed proposition, not a new assumption or hole. Both new theorems use the same named equation; its body contains no `sorry`. It has no users outside this new delivery, so no existing interface change or forced adaptation is involved.

## Second reading by F4

1. Interface: PASS. Read the unified diff against the read-only repository and
   compared the existing theorem signature byte for byte, including every let
   binding in its conclusion. It is identical. The only existing node fields
   changed are `proof`, `proof_deps`, and `proof_origin`. Public imports and
   visibility are unchanged; the local transparency settings are documented in
   `coord/changes/one-chart-lift-local-transparency.md`.
2. Kernel and construction: PASS. All four delivered modules compile locally
   in import order without warnings (3.6, 9.7, 2.9, and 37.4 seconds). The only
   two textual holes are the two reported named theorems, each exactly `by sorry`.
   No prohibited declaration or attribute occurs. A scratch module prints axioms
   for all four declarations: the target and two open lemmas use only the three
   permitted axioms and `sorryAx`; the recovery definition uses only the three
   permitted axioms. The target constructs its map by explicit conjugation inside
   an existential proof; no arbitrary unproved witness defines data.
3. Splits and sources: PASS as a decomposition. Read both complete docstring
   arguments and all new nodes. Checked Stacks Tags 01ZR and 05N7 (2) directly,
   and Tags 0095/0096 for pullback and adjunction. The stage charts are affine
   base changes of the selected affine chart over Spec R(j), so the first lemma
   is ordinary affine Hom descent. The second is a coherence identity for a
   supplied lift on an arbitrary triangle, with no descent assertion. Identity
   triangles, zero modules, empty affine charts and equivalent preorder indices
   introduce no exception; j makes the upper tail nonempty. Neither statement
   simply renames the target. Independent LeanFinder search for Hom/filtered
   colimits found ring and section results, not this sheaf Hom descent; Loogle
   found `Scheme.Modules.pseudofunctor_associativity`, which supplies ordinary
   coherence but does not state the mixed tensor identity. Searched both library
   roots for descent, recovery and transport; inspected FinitePresentationColimit,
   FiniteDescent, AffineChartDirectedRingModel and OpenCoverMapLiftTransport.
   These supply ingredients or different assertions, not a direct replacement.
   Neither remaining hole has a short direct proof from the available statements.
4. Route and pruning: PASS. The actual upper proof restricts the two sheaves,
   transfers the four instances, applies ordinary descent, constructs r, and
   applies triangle transport. Existing unit `sk-thm-picard-semicon` has empty
   `realized.statement` and an empty realization of its sole step; no unit route
   is bypassed or changed. The old direct proof dependencies
   `def-pc-fibre-product`, `def-pc-tensor-pullback-composition-iso`, and
   `lem-pc-fp-module-map-descent-affine` are absent from the new direct list but
   remain required below the split lemmas or in the unchanged signature. This is
   not global pruning. The removed direct FinitePresentationColimit import and
   its continuing lower use are already recorded under No longer needed.
5. DAG: PASS. Read all four delivered nodes and verified each recorded Lean
   signature occurs verbatim in its module. The new nodes contain their sources,
   complete statements, search records, provenance, blueprint ancestry and Lean
   records. Every proof-dependency list equals the union of its step uses; the
   existing node records the actual reduction. The recovery node has no proof
   obligations. One closed upper hole and two added lower holes remain net -1;
   no claim of a sorry-free target or positive net progress is made.

Changes by the second reader: added this independent review and made the exact
old-versus-new direct dependency comparison explicit. No Lean statement, proof,
import, definition or DAG repair was necessary. Scratch axiom checks are not part
of the delivery.
