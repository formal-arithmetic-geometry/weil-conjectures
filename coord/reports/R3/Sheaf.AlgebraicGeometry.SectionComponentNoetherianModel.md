## What changed

Repair of the duplicate-statement return: deleted all four private helpers in
`SectionComponentPullback`, and rewrote its public theorem as a direct proof in the given
cartesian square. Updated that node’s proof route. The original target proof and the
section-descent proof are unchanged. The previous second reading has been removed because
it reviewed the superseded version; the dispatcher must obtain a fresh second reading.

Proved `AlgebraicGeometry.exists_section_component_noetherian_model` in
`Sheaf.AlgebraicGeometry.SectionComponentNoetherianModel` without changing its signature,
visibility, universe, or existing docstring. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.SectionComponentPullback` and
`Sheaf.AlgebraicGeometry.SectionNoetherianDescent`.

The proof chooses an affine neighbourhood of the image of the supplied point, restricts
the morphism and section using the cartesian square's universal lift, and descends the
restricted morphism together with its section. Two applications of component compatibility
(one for the restriction square and one for the noetherian model square), followed by
transitivity and symmetry, give the requested equality of inverse-image loci.

Added two fully proved supporting modules:

- `SectionNoetherianDescent`: `AlgebraicGeometry.exists_noetherian_model_with_section`.
  Uses `Scheme.NoetherianApproximation.ofIsAffine` and
  `Scheme.exists_isPullback_of_finitePresentation`. Descends the section using Mathlib's
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` on the over category of the
  chosen stage. The factorization is over the original stage, so lifting it to the later
  source pullback gives a genuine section directly, without a separate equality-descent
  stage. The source is noetherian by locally finite type over the noetherian base and
  quasi-compactness.
- `SectionComponentPullback`: `AlgebraicGeometry.section_component_preimage_of_isPullback`.
  Proves the arbitrary cartesian-square statement directly using cycle-free foundational
  imports. The proof restricts the given square to the ambient open representing the old
  fibre component, uses geometric connectedness of that fibre with its rational point,
  and proves both inclusions by maximality of connected components. No private helpers,
  canonical-pullback reduction, or homeomorphism transport remain.

Read Stacks Tags 055P, 055M and 01ZM and their relevant first reduction/base-change/descent
arguments. Also read the TeX labels `more-morphisms-lemma-base-change-connected-along-section`
and `more-morphisms-lemma-connected-along-section-locally-constructible`. The route remains
inside the section-component step of the slicing unit; its unit's `realized` lists are empty.
No definitions or existing public interfaces changed; no forced adaptations or change
records are necessary.

All three delivered modules compile together in import order with `lcompile.py`, without
warnings. Unneeded explicit `PullbackCarrier` imports in the new modules were removed and
the set recompiled successfully. The delivery axiom probe passed for every delivered declaration, including the supporting theorems; only `propext`, `Classical.choice` and `Quot.sound` are used. An unnecessary
`open Limits` addition in the original module was removed after the first dry run flagged
it as an interface change; its original commands now remain unchanged.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.exists_section_component_noetherian_model`
(node `lem-sbc-section-component-noetherian-model`).

Also fully proved:
`AlgebraicGeometry.exists_noetherian_model_with_section`
(node `lem-sbc-affine-section-noetherian-descent`) and
`AlgebraicGeometry.section_component_preimage_of_isPullback`
(node `lem-sbc-section-component-cartesian`), with no private helper declarations.

No `sorry` remains in any delivered Lean file; no holes were added. This is a full proof,
not a decomposition into unproved statements. The third new node attaches the already proved
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section`; it adds no Lean file
or declaration.

Edge cases: neither the component lemma nor the descent lemma assumes smoothness, flatness,
reducedness, connectedness of the whole source, or injectivity of the base change. The empty
source/base case and the identity base change are allowed. In the component proof the section
point belongs to its fibre by the section equation; nonemptiness is derived from that point.
The arbitrary cartesian-square proof uses the square itself and section compatibility.
Models remain in
the same universe through the library's small affine noetherian approximation. Choices of
existential witnesses occur only inside proofs; no data definition selects an arbitrary
witness of an unproved existence theorem.

## No longer needed

Repair pruning: the four private helper declarations `component_canonical_pullback`,
`component_homeomorph`, `connected_fiber_baseChange`, and `exists_component_open` are
removed. No module or DAG node was attached to those private helpers. The canonical
pullback and homeomorphism-transport steps are unnecessary in the direct-square proof.
No supporting module or original statement import is removed.

None of the item's original imports, nodes or modules is pruned: the original node had no
proof-dependency nodes, and both original public imports are needed for its statement.
No new `sorry` dependencies are imported. The speculative explicit
`Mathlib.AlgebraicGeometry.PullbackCarrier` imports in the two new supporting modules were
removed because the remaining imports already provide all their needs.

`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` is not imported: it reaches this
item and would create an import cycle. The public theorem handles arbitrary cartesian squares directly; the four duplicate
helper declarations of the returned delivery have been deleted. No unit statement or step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's node carried its entire proof in one step with `uses: []` despite finite-presentation
descent and component base-change compatibility being the non-elementary steps. It now records
the actual two supporting theorems and the restriction/equality-composition glue.

The source library does provide finite-presentation descent and the canonical Tag 055M
component theorem. However, the latter lives in `SlicingFlat`, which imports `Slicing`, whose
smooth section-component proof reaches the assigned item. The import-direction tool rejects
that import. The return correctly identified four duplicate private helper statements. All four have
been removed: `component_canonical_pullback`, `component_homeomorph`,
`connected_fiber_baseChange`, and `exists_component_open`. No duplicate declaration is
retained under another name. The more general cartesian-square theorem is now proved
directly, without assuming a canonical pullback or invoking homeomorphism transport.
No library source or interface was changed; the source of the argument is credited.

Mathlib searches are recorded in `searches.jsonl`. LeanSearch returned Internal Server Error
and is reported as unavailable, not as a failed mathematical match. Loogle and LeanFinder
returned only more general topology/pullback/finite-presentation facts. Local source search
found the existing proved noetherian approximation/descent and rational-point connectedness
results, which the proof uses. The latter had no matching DAG declaration record, so it is
attached by the third new node rather than restated in Lean.

## New nodes

`lem-sbc-affine-section-noetherian-descent` records the proved section-compatible noetherian
cartesian model over an affine base, in
`lean/Sheaf/AlgebraicGeometry/SectionNoetherianDescent.lean`. It realizes the approximation
half of Tag 055P's first reduction and cites the existing affine approximation,
finite-presentation descent and morphism-descent nodes as tools. The existing closed
noetherian approximation/descent nodes belong to other units; they are tools, and the
slicing unit's route is unchanged.

`lem-sbc-section-component-cartesian` records the proved inverse-image equality for a general
cartesian square with compatible sections, in
`lean/Sheaf/AlgebraicGeometry/SectionComponentPullback.lean`. It realizes Tag 055M, the
component half of the noetherian-model proof. It requires locally finite type and uses an
open representative of a fibre component. The repaired node records the direct argument
in the given square rather than a canonical-pullback reduction and homeomorphism transport.

`lem-sbc-connected-rational-point-geometrically-connected` attaches the existing proved
`AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected` (Stacks 04KV,
`varieties-lemma-geometrically-connected-if-connected-and-point`). No Lean file is added for
this node; its statement is the rational-point criterion used by the component argument.
Searches of all imported blueprint nodes for connected components and finite-presentation
descent found no exact blueprint node for either new combined supporting theorem. The
existing descent nodes are retained and cited, not duplicated.


Repair validation: all three modules compile without warnings. The delivery axiom probes
passed, and `deliver3.py --no-push` printed OK (awaiting the new second reading only).
No delivery was pushed.


## Second reading by R3

1. **Interfaces: pass.** Diffed the existing module and node against the repository.
   The theorem signature, universe, visibility, commands and existing docstring are
   byte-for-byte unchanged. Only its proof and two plain proof imports changed. The
   other two Lean modules are new; no definitions or other existing modules changed.
   The existing node changes only proof, proof_deps and proof_origin.
2. **Proof and trust: pass.** Independently compiled all three current modules in import
   order with lcompile.py; no errors or warnings. Scanned the delivered Lean sources:
   no sorry, axiom, unsafe, opaque, extern, implemented_by or kernel-check bypass.
   Replaced stale scratch probes with copies of the current modules and compiled them
   together. Each of the three public theorems prints exactly propext, Classical.choice
   and Quot.sound, with no sorryAx. All witness choices are local to proved theorems;
   no data definition or arbitrary witness from an unproved existence result is added.
3. **Supporting statements: pass.** No unproved statements are split off. Read both new
   supporting proofs: the component proof constructs a rational point of the restricted
   residue-field fibre and uses geometric connectedness before maximality in each
   direction; the descent proof factors the section over the old stage and lifts it
   to the later pullback, proving both compatibility and the section equation. Identity
   base change and disconnected sources are covered without additional assumptions;
   the empty-base case is allowed and the target's empty-source case has no supplied p.
   Repeated searches with new wording through LeanFinder, Loogle and Mathlib grep, and
   searched lean/ directly. The canonical SlicingFlat theorem is unusable through the
   cyclic import; the existing Smooth.section_component_iff_of_isPullback and smooth
   model data require Smooth and cannot prove this locally-finitely-presented item.
   The rational-point criterion is attached to its existing declaration, not duplicated.
4. **Route and pruning: pass.** Read the Tag 055M proof and Tag 055P first reduction in
   the local Stacks TeX. The two applications of component compatibility and affine
   descent follow that route. All plain imports supply proof API; public imports supply
   the signatures. The original proof_deps was empty, so no old dependency node is
   omitted from No longer needed. The report correctly records the removal of four
   obsolete private helpers and redundant PullbackCarrier imports. Read
   dag/units/sk-prop-normal-form.json: its realized lists are empty and its slicing
   step is preserved; no unit statement or step is bypassed.
5. **DAG: pass.** Read all four delivered nodes, checked each proof_deps against the
   union of step uses, and checked the Lean attachments and new-node fields. The target
   node records affine restriction, section descent and the two component equalities.
   The supporting nodes record the actual direct-square and later-stage pullback
   arguments and their existing approximation/geometric-connectedness tools.

Second reading changed only this report and refreshed scratch axiom probes; no delivered
Lean proof, statement, import or node needed repair. Independently verified one original
hole closed, zero holes added, and two fully proved supporting theorems.
