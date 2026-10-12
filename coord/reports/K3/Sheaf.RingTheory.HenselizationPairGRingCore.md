## What changed

Replaced the sorry in `RingTheory.henselization_pair_noetherian_and_maximal_regular`
with a complete Lean proof, keeping its statement and visibility identical. Added
`Sheaf.RingTheory.PairHenselizationRegularFibers`, with the single intermediate theorem
`RingTheory.pair_henselization_regular_fibers`.

The proof obtains Noetherianity and flatness from the existing
`pair_henselization_noetherian_completion`. For each maximal ideal m it constructs
representatives modulo IB from the supplied quotient bijection. Henselianness gives
IB contained in m. These representatives prove extension of the contracted prime is m
and surjectivity of the map of local residue fields; injectivity follows from locality.
The existing `flat_local_completion_iso` then gives the compatible completion equivalence.
The proof composes the regular localization with the base's regular local completion map,
transports regularity along the equivalence, and applies the new fibre-transfer statement.
Flatness of localization and completion gives a regular global map from the henselization
to this completed local ring. Regular-through-localization yields the requested regular
local completion map.

Updated the item's DAG proof and dependencies to this argument. Added the new node with
a source, four proof steps and actual recorded searches. No statement or definition was
changed, and no other existing module was adapted. Both modules compile without warnings
using the prescribed `lcompile.py --all` invocation (about 3 and 26 seconds).

## Proved and sorry left

Closed the original hole in
`RingTheory.henselization_pair_noetherian_and_maximal_regular`
(node `lem-weil-pbc-henselization-pair-g-ring-core`); no sorry remains in the item.

Added one hole:
`RingTheory.pair_henselization_regular_fibers`
(node `lem-weil-pbc-pair-henselization-regular-fibers`), in the new module. Its proof is
exactly `:= by sorry`. This is a decomposition, not a claim of a net hole reduction:
one original hole closed, one lower hole added. The other dependencies retain their
existing proofs and holes.

The new lemma is strictly the fibre calculation. It has an arbitrary ring C and map
B to C with regular composite A to C. It assumes neither a G-ring nor a henselian
pair property nor a completion nor flatness of B to C, and it concludes only geometric
regularity of fibres, rather than Noetherianity and regular local completion maps.
The item's proof supplies the regular composite through an explicit completion
comparison and proves the required flatness and localization cancellation separately.

Edge cases checked mathematically: for I=0 the diagram consists of ring isomorphisms
and the fibre-transfer lemma reduces to the composite's fibre clause. For I=A the
colimit is the zero ring and has no primes to check. A zero target C gives zero fibres,
whose prime-local regularity is vacuous. For a general prime q, the fibre product of
Tag 0AH1 is nonempty because q itself is a factor; other components may be zero after
tensoring with C. The argument allows all these cases and imposes no finiteness of
the separable algebraic residue-field extensions.

## No longer needed

Removed the item's direct proof imports
`Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit` and
`Sheaf.RingTheory.GeometricRegularitySeparableExtension`. Their nodes
`lem-weil-pbc-henselization-finite-separable-fibres` and
`lem-weil-pbc-geometric-regularity-separable-extension` remain needed by the new
fibre-transfer node; they have been relocated in the proof plan, not globally pruned.
No mathematical node or module is claimed to leave the targets' closure.

Retained both existing public imports. In particular,
`Sheaf.RingTheory.GRingMaximalIdealCriterion` is the existing public path to the G-ring
notions and also exposes the maximal-ideal criterion used by the parent module.
The parent theorem still applies that criterion; its unit route is preserved.
All newly added private imports are used by the proof, and the new module uses public imports only for its statement. Its planned
proof dependencies are private imports, restored at second reading.

## Where the brief, the DAG or earlier work was wrong

Repair of the return at head 43dae26ba: the reviewer accepted the mathematics, but
landing attempted to read the absent unrelated module
`Sheaf.Topology.NestedSliceExtensionStalkIso`. Neither delivered module imports it,
and neither node lists it as a dependency. No topology module is added or adapted
in this repair. The prescribed delivery tool rebuilds the commit on freshly fetched
`origin/sheaf-dag`; the repair reruns local compilation and explicitly enables the
server compilation check with `WEIL_SERVER_COMPILE=1`. This report records the
returned landing failure rather than treating a rebase as a mathematical repair.
The original independent second reading below records the previous delivery only;
the repaired delivery remains for the next independent reader. The decomposition
still closes one original hole and introduces one strictly lower fibre-calculation
hole, with no change of signatures, definitions, or proof dependencies.



Repair verification: the fetched base was `e86bfd7bcb3bac2a3f59e354bfbf5879c175d0fd`.
Its `tools/stage3_delivery.py` now catches `FileNotFoundError` in `scan_imports`
and skips absent paths in `downstream_users`, so scanning the missing unrelated
module no longer aborts preflight. These are existing upstream fixes, not edits in
this delivery. With `WEIL_SERVER_COMPILE=1`, dry run `1a79ef6f7` printed OK:
the two-module local compile, axiom checks, server check of the dependency-free
new module, and refreshed-base preflight all passed. The delivery tool compiles
the core locally against the new module; it skips that core in its server loop
because the new module is not landed there yet. The next global build verifies
the delivered set on the server. One earlier local compile hit the 60-second limit;
the dry run's subsequent fresh compile passed the unchanged proof within its limit.
No push was made.

The old core node compressed the whole argument into a single step. Its cited theorems
provide Noetherianity, a conditional completion comparison, the finite product of residue
fields and separable base-field transfer. They do not supply the tensor-product/direct-factor
calculation as a Lean declaration. The new fibre-transfer node isolates that missing bridge.
The omitted local completion comparison is proved in the item, including maximal-ideal
extension and residue-field bijectivity; no hypothesis was added to get it.

The local literature checkout lacks `literature/stacks-project/more-algebra.tex`.
Read the authoritative pages https://stacks.math.columbia.edu/tag/0AH3,
https://stacks.math.columbia.edu/tag/0AH1 and https://stacks.math.columbia.edu/tag/07QH
instead. The new lemma generalizes precisely the displayed tensor calculation in 0AH3,
replacing its completed ring by an arbitrary ring C; no step uses a completion property.

`blueprint_refs.py ancestor lem-weil-pbc-henselization-pair-g-ring-core` returned None:
the core's `created.item` is a module name, so the script cannot traverse its ancestry.
The new record follows the documented ancestry of the existing parent node to
`thm-weil-pbc-finite-etale-lifting`, through its essential-surjectivity proof step 7.
The blueprint-wide searches for 'henselization' and 'regular fibres ind etale' found
no imported blueprint node stating the new fibre-transfer lemma.

LeanSearch returned Internal Server Error; this is recorded as unavailable, not as a
negative search result. LeanFinder returned etale descent/composition declarations,
and Mathlib grep found no geometric-regularity/henselization theorem. Searches of
both library roots likewise found no ready-made cancellation theorem.

## New nodes

`lem-weil-pbc-pair-henselization-regular-fibers`, in
`Sheaf.RingTheory.PairHenselizationRegularFibers`, states the geometric regularity of
fibres of B to C when B is the Noetherian pair-henselization colimit and A to C is
regular. Its source is the product-of-fibres calculation in Stacks Tag 0AH3, with
Tags 0AH1 and 07QH. Its four steps obtain the finite residue-field decomposition,
tensor it with C, pass geometric regularity to the selected idempotent factor,
and transfer the base field along the separable algebraic residue-field extension.
The docstring gives this whole argument; the node records the actual searches.
No change record is required: existing interfaces and definitions are identical.

## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository by `diff` and compared the full existing
   theorem signature as raw text: byte-identical. The two existing public imports,
   universe and visibility are retained. There are no changed definitions, existing
   signatures, adapted modules or undeclared interface changes. Verdict: pass.
2. Compiled both modules in dependency order with `lcompile.py --all`, then compiled
   scratch copies with `#print axioms` for both declarations. Both compile without
   warnings; both axiom lists are exactly propext, Classical.choice, Quot.sound and
   sorryAx. The only delivered sorry is the named fibre theorem listed above; there
   are no forbidden declarations or data holes. The completion homomorphism obtained
   from flat_local_completion_iso is determined by that theorem's evaluation clause:
   every quotient evaluation has a representative from the original ring, and equal
   evaluations at every n determine an element of the completion. Thus this is not
   an arbitrary object selected from a mere existence theorem. Verdict: pass.
3. Independently read Stacks https://stacks.math.columbia.edu/tag/0AH3,
   https://stacks.math.columbia.edu/tag/0AH1 and
   https://stacks.math.columbia.edu/tag/07QH. The finite product decomposition is
   compatible with the B action, so tensoring over B and selecting the q component
   gives the stated fibre. Projection onto a component is idempotent localization,
   including after purely inseparable base change; Noetherianity descends through
   its surjection. Separable algebraic field ascent then supplies the conclusion.
   Checked I=0, I=A, zero C and zero individual components. No finite-degree
   assumption on the residue extension is needed. The new statement isolates only
   fibres, not the original Noetherianity/completion theorem, and is strictly a part
   of its argument. Repeated searches with different words: LeanFinder query
   "geometric regularity cancellation along weakly etale homomorphism with noetherian
   source" returned etale composition/cancellation results only; Mathlib grep for
   formally etale and ind-etale regularity found no match. Searched both local library
   roots and read RegularPermanence and GRingCompletionRegular: their descent is
   across the other side of the diagram and does not replace this fibre calculation.
   The docstring proof and complete new node match. Verdict: pass; the hole is not
   something that can be closed in a few minutes with an existing theorem.
4. Read the proof from its conclusion through localization cancellation, regular
   composite transport, the commuting completion comparison, and quotient
   representatives. The shorter existing routes found do not prove these fibres.
   All old proof_deps are accounted for: the Noetherian and completion-iso nodes
   remain direct dependencies; the finite-separable and separable-extension nodes
   move below the fibre node. Read sk-thm-p1.json realized and the existing parent
   route; neither is bypassed or changed. No global module pruning is claimed.
   Found and repaired missing private imports of the new node's documented proof
   dependencies, so these dependencies remain in the import closure. Verdict: pass
   after repair.
5. Compared each revised core proof step with the actual Lean terms and checked its
   proof_deps is the union of step uses. Checked the new node's fields, source,
   ancestry, Lean statement and four docstring proof steps. Existing node changes
   are restricted to the stage-3-owned proof fields. Verdict: pass.

Second reading changed only the new fibre module's private proof-dependency imports
(PairHenselizationFiltered, FiniteSeparableFibersOfEtaleColimit,
LocalizationOfRegularRing, GeometricRegularitySeparableExtension, TensorProduct.Maps,
TensorProduct.Pi and Noetherian.Basic) and this report. Recompiled the repaired set:
3.3 seconds for the fibre module and 26.9 seconds for the item. One original hole is
closed and one lower hole added: this remains a decomposition with zero net holes
closed, not a sorry-free proof of the target closure.


## Second reading by K3

This is the independent second reading of the repaired delivery, performed from
its sandbox and the current repository; the earlier reading above is historical.

1. Compared the delivered core with the repository using diff and compared its
   full theorem signature as raw text: byte-identical. Its existing public imports,
   visibility and universe remain identical. No existing definition or statement
   changes, no forced adaptations, and no change record is needed. Verdict: pass.
2. Compiled both delivered modules with the prescribed lcompile.py --all: clean,
   2.5 and 18.9 seconds. Independently compiled scratch copies with #print axioms:
   each declaration uses only propext, Classical.choice, Quot.sound and sorryAx.
   The sole delivered sorry is the complete proof of the named fibre theorem;
   no forbidden declaration or data hole occurs. The completion map selected from
   flat_local_completion_iso is uniquely determined by its evaluation clause:
   each quotient evaluation has a representative, and all evaluations determine
   an element of the completion. Selecting it introduces no arbitrary data from
   mere existence. The choices hc.1.some are proofs of IsColimit. Verdict: pass.
3. Read the new theorem, its entire docstring and node against Stacks Tags 0AH3,
   0AH1 and 07QH. The canonical fibre decomposition respects the B action;
   tensoring over B with C identifies the composite fibre with the finite product
   of B-to-C fibres. The chosen component is an idempotent localization, also
   after finite purely inseparable extension, and is Noetherian as a quotient.
   Separable algebraic residue-field ascent then gives precisely the statement.
   Checked I=0, I=A, zero C and vanishing components. No finite-degree assumption
   is needed. This fibre-only assertion is strictly a part of the original proof.
   Repeated LeanFinder search with "geometrically regular algebra cancellation
   along an ind etale base ring map" found etale composition/base-change results,
   not this assertion. Mathlib grep and independent rg over both library roots
   found no replacement; RegularPermanence cancels on the other side of the
   diagram. Closing this hole requires formalizing the product calculation and
   category/colimit transport, not a short application of an existing result.
   Verdict: pass; retain the explicitly reported decomposition.
4. Read the proof from the final localization cancellation back through flatness,
   fibre transfer, regular composition, compatible completion comparison and the
   quotient representatives. Each private core import supplies a used theorem or
   instance; the new module imports its documented proof dependencies privately.
   All four old proof dependencies are accounted for: Noetherianity and completion
   comparison stay direct, finite-separable fibres and separable transfer move
   below the new node. No module is globally pruned. Read sk-thm-p1 realized and
   the parent isGRing_of_pair_henselization: the maximal-ideal criterion and the
   unit's route are preserved. Verdict: pass.
5. Compared the existing node JSON field by field: only proof, proof_deps and
   proof_origin differ. Both nodes have proof_deps exactly equal to the union of
   their step uses. Checked those uses against their Lean declarations or Mathlib
   matches, and checked the new node's source, ancestry, searches, status, created,
   chapter/unit and Lean statement against its module. Verdict: pass.

Second reading changed only this report, adding the current independent audit.
No Lean or node repair was necessary. One original hole closed and one strictly
lower hole added; net hole reduction is zero. The target closure remains open.
