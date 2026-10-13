## What changed

Proved `AlgebraicGeometry.exists_affine_chart_upper_tail_limit` without changing its
signature, visibility or docstring. Its only added import is the proof-only import
`Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitComparisons`.

The new Data module constructs the actual upper-tail spectrum diagram and cone in
the slice, then defines the chart diagram and cone by applying slice pullback and
forgetting. These definitions contain real data and proofs; none chooses an
arbitrary witness of an unproved existence theorem. The new theorem
`AlgebraicGeometry.upperTailChartCone_isLimit` proves this particular cone limiting
using cofinality, reflection of limits, and preservation of limits. Stage
affineness is proved directly in the item with Mathlib's affine pullback instance.

The new Comparisons module proves its comparison isomorphisms and both equations
for this explicit cone using Mathlib pullback symmetry and pasting. Its statement
needs neither a directedness assumption nor a limiting/affineness assumption.
Both new modules have public imports only for their statements/definitions; the
three Mathlib imports used only in the Data limit proof are plain imports.

## Proved and sorry left

Closed the one baseline hole:
`AlgebraicGeometry.exists_affine_chart_upper_tail_limit`
(node `new-affine-chart-upper-tail-limit`).

Added and proved `AlgebraicGeometry.upperTailChartCone_isLimit`
(node `new-affine-chart-upper-tail-limit-data`) and
`AlgebraicGeometry.affine_chart_upper_tail_limit_comparisons`
(node `new-affine-chart-upper-tail-limit-comparisons`). No holes are added or left
in any of the three delivered modules. This is a proof, not a decomposition with
new holes: one baseline hole closed, zero holes added, net one. The original
sandbox's sorry declarations were never landed; the meaningless data-existence
lemma is replaced by explicit constructions and their proved limiting property.

The target's `#print axioms` in a scratch copy lists exactly `propext`,
`Classical.choice`, and `Quot.sound`. All three modules compile without warnings.

## No longer needed

No original module import is removed and no module is claimed as globally pruned.
The sandbox's redundant direct Data import in the target was removed: the one
proof-only Comparisons import provides its public Data dependencies.

Every old proof dependency was inspected. `def-pc-fibre-product` remains used for
the pullbacks and stage-affineness argument. `def-pc-base-change` is no longer a
direct dependency of the target's reduction, so it is removed from that node's
`proof_deps`; it remains in the unchanged statement dependencies and in the
comparison node's proof dependencies because the equations use `baseChangeMap`.
Neither convention node nor its module is globally pruned. The target's new direct
proof dependencies are the two new nodes and `def-pc-fibre-product`.

## Where the brief, the DAG or earlier work was wrong

The initial comparison lemma was false: it accepted any affine diagram with a
limiting cone, with no relation between that diagram and the specified charts.
For a singleton index, a fixed nonempty affine chart and a constant diagram at the
empty affine scheme satisfy its diagram/limit/affineness assumptions, but its
claimed stage isomorphism would identify an empty scheme with a nonempty scheme.
The original data-existence lemma imposed no relationship at all on its witness
and could likewise be satisfied by an irrelevant constant diagram. The report's
claim that these two statements formed a valid decomposition was therefore wrong.

The repair constructs the intended diagram and cone, proves their limit property,
and proves the comparisons for exactly those objects. This changes only new,
unlanded sandbox declarations, with no existing signature or definition changes
and therefore no change record or forced adaptations.

The literature source files are absent on this machine. Stacks Tag 01ZR was read
from its official page: its first proof motivates affine reduction. The concrete
categorical argument here is fully checked against the pinned Mathlib sources:
`Monotone.final_functor_iff`, `Functor.Initial.isLimitWhiskerEquiv`, the slice
forgetful functor's connected-limit instances, the pullback adjunction, and
`pullbackRightPullbackFstIso`. Searches in Mathlib, upstream and local Lean found
supporting constructions, which the proof uses, but no duplicate chart theorem.
LeanSearch was unavailable; the actual failed searches and the successful
LeanFinder/Loogle/grep searches are recorded, without invented results.

## New nodes

`new-affine-chart-upper-tail-limit-data` records the four explicit diagram/cone
constructions and the fully proved `upperTailChartCone_isLimit`. Its Lean signature
is copied from the delivered declaration, and its proof describes the actual
cofinality and preservation/reflection argument.

`new-affine-chart-upper-tail-limit-comparisons` records the fully proved comparison
lemma for the specified cone. Its statement, signature, dependencies and proof
are corrected to match the construction and the Lean projection calculations.
There are no change records. The existing item's node changes only `proof`,
`proof_deps` and `proof_origin`.

## Second reading by R3

1. Compared the original and delivered target module by `diff`, and separately
   asserted exact byte equality of its theorem signature through `:= by`.
   Verdict: its only changes are a plain proof import and its proof. No existing
   statement, definition, visibility or docstring changes; no forced adaptation.
2. Compiled all three files in import order with the required launcher. Inspected
   all delivered source for `sorry`, forbidden declarations and hollow definitions.
   Added `#print axioms` to scratch copies. Verdict: no errors or warnings, no
   `sorry`, no forbidden axiom/escape, and only the three permitted axioms.
3. Tested the first worker's split statements on singleton/empty-scheme cases and
   rejected the arbitrary-diagram comparison. Replaced the data-existence hole
   with explicit pullback constructions, restricted the comparison to that cone,
   and proved both auxiliary statements. Repeated searches using different
   wording via LeanFinder, Loogle and grep, plus LeanSearch (unavailable), and
   searched upstream and local Lean. Verdict: all statements now proved, no new
   hole or duplicate theorem. Empty charts and equivalent preorder indices are
   covered by the categorical proofs; the upper tail is nonempty because of i.
4. Inspected the top-down reduction, imports and every old proof dependency.
   Used Mathlib's cofinality/pullback API and affine pullback instance directly.
   Removed the redundant direct Data import and documented the old dependencies
   above. Inspected `dag/units/sk-thm-picard-semicon.json`: its `realized` fields
   name no nodes, and the affine base-change route stays the same. Verdict: no
   unit step bypassed and no unsupported pruning claim.
5. Matched both new nodes' signatures to the delivered Lean, recorded the real
   searches and constructions, and updated the existing node's route to the
   actual proof. Checked new nodes' chapter/unit/creation/blueprint fields and
   each `proof_deps` union. Verdict: DAG and Lean agree.

Second reading changed the invalid arbitrary-diagram decomposition to an explicit,
fully proved construction, proved both auxiliary lemmas, narrowed imports,
updated all proof/node metadata, and rewrote this report with the actual hole count.
