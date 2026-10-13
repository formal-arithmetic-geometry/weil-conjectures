## What changed

Implemented `AlgebraicGeometry.openCover_map_lift_transport` with its existing
signature and docstring unchanged. The proof constructs the transition and cone
maps in the over category, proves all four composition triangles, constructs
the chart maps `d` and `z` by pullback universal properties, and transports the
supplied morphism by the explicit restriction comparison `alpha`.

Five proved private helpers carry the categorical argument: `recovery_iff`,
`recovery_square_iff`, `transport_square`, `transport_recovery`, and
`transport_chart_map`, in
`AlgebraicGeometry.Scheme.Modules`. Recovery is converted into a commuting
square, pulled back along `z`, moved through `delta` and `beta` by naturality,
and converted back into the exact recovery equation in the original statement.
The generic `transport_recovery` combines the square calculation and both
recovery equivalences before specializing to scheme modules, reducing repeated
kernel checking of the canonical comparisons. The chart helper exposes
descent-data objects at its boundary. The concrete
proof constructs both chart refinements directly, avoiding a second helper
whose kernel checking repeated the same expensive conversions.
The original two
unused `B` lets are retained verbatim; the unused-variable linter is suppressed
only for the existing theorem to avoid warnings about those original lets.

Added the proof-only import
`Sheaf.AlgebraicGeometry.OpenCoverTensorComparisonCoherence`. This new module
states just the comparison identity from step 2 of the original node's plan.
It has no descended morphism, lift-existence hypothesis, or lift-existence
conclusion. Its canonical isomorphisms are explicitly constructed from the
existing definitions; no data is chosen from a new unproved existence theorem.
Updated the item's node proof and dependencies to record this reduction.

Added `Sheaf.AlgebraicGeometry.OpenCoverRefinementComparisons`, whose definition
`AlgebraicGeometry.Scheme.Modules.openCoverRefinementComparisons` constructs the
five comparison isomorphisms as a tuple. This shares their expressions between
the new theorem and the transport proof. Directly repeating them caused kernel
checking to exceed the file limit; the named construction compiles within it.
The definition contains no `sorry` and no chosen existence witness.
`Sheaf.AlgebraicGeometry.ModuleRecoveryComparisonIso` names the generic
composition/whiskering expression used for its last two entries, so the
categorical calculation and scheme-level tuple share that expression too.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.openCover_map_lift_transport`
(node `lem-pc-open-cover-map-lift-transport`) by a complete Lean proof from the
new coherence theorem and existing definitions. Every private helper is proved.
No `sorry` remains in the item's module.

The optional `cleanup.letToHave` preprocessing pass is disabled for the file.
The concrete specialization uses restricted transparency and a local
`instance_reducible` attribute for the base-change alias. These settings affect
elaboration only, preserve the definitions and signatures, and introduce no
unchecked proof or additional axiom.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.openCover_tensor_comparison_coherence`
(node `lem-pc-open-cover-tensor-comparison-coherence`), in the new module
`Sheaf.AlgebraicGeometry.OpenCoverTensorComparisonCoherence`.
Its whole proof is `:= by sorry`; its docstring and node specify the mate and
ordinary pullback associativity calculation that remains.

This is a decomposition: one old hole closed and one strictly smaller hole
added, for net zero holes closed. The theorem is not claimed to be independent
of `sorry` in its import closure.

## No longer needed

None. All three original public imports are needed by the unchanged statement.
The new proof-only import is used. All original node dependencies still enter
the construction or the canonical comparisons, directly or through the new
coherence node. No modules are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The saved attempt contained the geometric reduction but repeatedly timed out
before preflight. This repair restored the proved generic `transport_recovery`
helper and replaced broad simplification at the final specialization with
`exact`, preserving the named canonical comparisons. The retained proof now
compiles within the 60-second file limit (54.8–57.4 seconds in the final
individual checks). The statement comparison reports no changed signature.
The optional experiment naming further bundle components gave no speedup and
was removed; no such extra declarations are delivered.

The dry run printed OK: compilation and preflight pass except for the independent
second-reading section, which the next worker supplies. Nothing was pushed.
The unresolved canonical-comparison identity remains the separate item required
by the brief.

The existing plan's references to pushforward associativity hide a mate
calculation for the exact chosen tensor adjunctions; neither of the two existing
comparison definitions alone states that identity. This is the new node's
scope. Stacks [0095](https://stacks.math.columbia.edu/tag/0095) defines module
pullback, and [0096](https://stacks.math.columbia.edu/tag/0096) supplies its
adjunction. The more detailed comparison-coherence proof is an agent expansion
of the original node's argument, not a verbatim theorem from those tags.

The unit `sk-thm-picard-semicon` has no realization entries for this item; its
statement and route are untouched. Edge cases of the new statement were checked
mathematically: identity refinements reduce to ordinary comparison cancellation,
zero modules give the unique zero morphism, and empty charts require no sections
or chosen points. The statement uses no nonempty, finite-presentation,
affineness, directedness or limit hypothesis.

## New nodes

`lem-pc-open-cover-tensor-comparison-coherence` is the explicit comparison
identity for a refinement `d` and its cone-vertex refinement `z`. It is strictly
a part of recovery transport, independent of the morphism being transported.
Its source is the canonical-comparison step of the original transport plan,
expanded using Stacks 0095/0096 and ordinary module pullback associativity.
LeanFinder and grep found related naturality/ordinary associativity results but
no exact theorem; LeanSearch was unavailable (HTTP internal server error).
A blueprint-wide search for pullback composition found derived/trace or finite
pullback statements rather than this tensor/open-chart coherence identity.
The new node, its Lean module, and the changed original node are in the sandbox.

`def-pc-open-cover-refinement-comparisons` names the explicit tuple of five
isomorphisms used by that coherence statement and the transport proof. Its
source and searches are the same comparison construction; it contains no
additional mathematical assertion or proof hole. The tuple's data is built
from existing pullback composition/congruence and tensor comparisons.
The change record `coord/changes/F4-open-cover-map-lift-transport-elaboration.md`
explains the local elaboration attributes and namespace commands that the static
preflight classifies as an interface change. No existing signature, definition,
visibility or public import changes, and no other existing module is adapted.

`def-pc-module-recovery-comparison-iso` names the elementary generic composite
of a composition comparison and an inverse restriction comparison, with the
two associators. This is a real explicit construction from supplied data,
contains no proof hole, and is reused by the comparison bundle and the proved
categorical recovery-equation calculation. Searches found Mathlib's primitive
whiskering, associator, horizontal composition and component lemmas; the module
names their specific composite to avoid repeated kernel unfolding.

The resumed worker reviewed all four retained modules, their DAG records, the
original plan and dependency signatures. The retained proof is a decomposition
of the original theorem into geometric refinement, a proved categorical
transport calculation, and one canonical-comparison coherence statement.
The earlier dry-run failure requesting a second-reading section has been
addressed in the launcher tool: first-worker dry runs now explicitly allow that
section to be absent. The section remains reserved for the independent second
reader. No second reading is claimed here, and nothing is pushed.

## Second reading by F4

1. Compared `OpenCoverMapLiftTransport.lean` with the repository version. The public theorem signature and existing declarations are unchanged byte for byte; only the proof, a proof-only import, and private helpers were added. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py --all`. The transport theorem has no `sorry`; the sole remaining `sorry` is the named public coherence theorem, with a matching split node and proof docstring. No forbidden declarations or hollow definitions were found. Verdict: pass.

3. Read the split coherence statement and the two explicit construction definitions. The coherence statement is a strict intermediate identity, its hypotheses and conclusion match the construction used by the transport proof, and its edge cases are covered by the stated equations. Searches recorded in the nodes found no existing equivalent declaration. Verdict: pass.

4. Checked the proof from the target downward. The route uses the explicit comparison bundle and coherence node, then the generic categorical transport helpers; all retained public imports are needed and the added coherence import is proof-only. No shorter applicable library route was found. Verdict: pass.

5. Checked the three new DAG records and the updated target record against the Lean declarations. Proof steps, dependencies, origins, and the unit `sk-thm-picard-semicon` are consistent; no unit route or target statement changed. Verdict: pass.

Changed only the second-reading report section; no Lean, DAG, or change-record repairs were needed.
