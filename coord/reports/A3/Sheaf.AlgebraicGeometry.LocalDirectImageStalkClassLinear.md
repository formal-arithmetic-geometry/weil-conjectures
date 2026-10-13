## What changed

Proved `AlgebraicGeometry.localDirectImage_stalk_class_smul` in
`Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassLinear`, with its signature,
visibility, existing docstring, definitions and imports unchanged. Added two proved
private helpers: `resolution_top_smul` for the arbitrary-morphism top-section
resolution comparison and `local_germ_smul` for the pushforward germ on the local spectrum.
The first uses equality of scalar natural transformations on the common additive
section short complex and Mathlib's `ShortComplex.homologyMap_mapNatTrans`.
The second uses `Scheme.fromSpecStalk_app`, restriction linearity and
`PresheafOfModules.germ_smul`. Their composition with `Hom.app_smul` proves the
specific constructed map's scalar compatibility. The larger heartbeat limit is
local to the first private proof; no file-level options were added.

Updated the existing node's proof and proof_origin to record this implementation.
The exact-functor comparison dependency remains a Mathlib leaf; it requires no new import.
No unit statement or realized unit step is bypassed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.localDirectImage_stalk_class_smul`
(node `lem-weil-pbc-local-direct-image-stalk-class-smul`).
Both private helper proofs are complete. No `sorry` remains in the delivered module;
no holes were added or split off. This is a proof, not a decomposition into holed lemmas.
The pre-existing dependencies used to construct module cohomology and the class map
are unchanged; this delivery does not claim to discharge their own holes.

## No longer needed

No imports, dependency nodes or modules were pruned. The existing proof_deps are
still needed. The closed-point detour in the original prose plan is unnecessary:
`Scheme.preimage_eq_top_of_closedPoint_mem`, `Scheme.germ_stalkClosedPointTo`, and
`Scheme.stalkClosedPointTo_fromSpecStalk` are not used. These are Mathlib lemmas,
not outstanding project modules. The searched `ResolutionSectionScalarMap` module
is not imported: its restricted-resolution interface would add transport work,
whereas the top-section scalar calculation is proved directly here.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The plan's assertion that the inverse-image
open must first be identified with top is stronger than the germ argument needs.
`Scheme.fromSpecStalk_app` already supplies the scalar identity on every relevant
inverse-image open. The node copy records this simplification. Existing declaration
docstrings were preserved.

The scalar calculation uses the RingCat scalar structure of the global-section
complex when forming the forgetful scalar natural transformation; using the
CommRingCat view there caused a Lean instance mismatch during development.
The final proof uses the original module structures throughout.

## Second reading by A3

1. **Interface: pass.** Compared the sole delivered Lean module with the repository
   using `diff`. The existing `localDirectImage_stalk_class_smul` signature is
   byte-for-byte identical, as are its visibility, docstring and imports. No
   definition was changed. The only added declarations are two proved private
   helpers. Checked the specified additive construction in
   `LocalDirectImageStalkClassMap` and the `resolutionSectionClass` definition in
   `FlatBaseChangeOpenChoices`: the final proof unfolds precisely that composite.
   Read [Stacks 01E4](https://stacks.math.columbia.edu/tag/01E4) and the local-ring
   comparison in [Stacks 02OD](https://stacks.math.columbia.edu/tag/02OD).
   The properness/coherence/Noetherian hypotheses of the latter's formal-functions
   theorem are not required for this scalar identity, which uses only the
   section-complex construction. There is no invertibility claim here.
2. **Proof and axioms: pass.** Compiled the delivered file locally with
   `lcompile.py`: no errors or warnings (45.8 seconds). Compiled a scratch copy
   with `#print axioms` for `resolution_top_smul`, `local_germ_smul` and
   `localDirectImage_stalk_class_smul`: each uses exactly `propext`,
   `Classical.choice`, `Quot.sound`, without `sorryAx`. No `sorry`, forbidden
   declaration form or new definition occurs in the delivery. In the first
   helper, degreewise equality of scalar natural transformations is transported
   by `homologyMap_mapNatTrans` and conjugated by the two homology comparison
   isomorphisms. The linear resolution comparison and theta finish the argument.
   In the second, `fromSpecStalk_app` identifies the restricted scalar, then
   `map_smul` and `germ_smul` prove the identity. The final theorem composes these
   identities with `Hom.app_smul`.
3. **Split statements: pass, none.** No new holed statement, module or node was
   introduced. Both helpers are fully proved and strictly intermediate. Checked
   degree zero, zero coefficients and an empty fibre product: the proof uses
   no positive-degree, nonzero or nonempty assumption. The point y already
   rules out an empty Y; no extra exclusion is introduced. No data is selected
   from an arbitrary unproved existence theorem.
4. **Shortest route, imports and unit: pass.** Searched the library for
   `resolutionSectionClass`, `sectionCohomologyTheta`, scalar comparison and the
   local class map, and independently searched Lean Finder for scalar
   multiplication under homology/evaluation comparisons. Inspected Mathlib's
   `homologyMap_mapNatTrans` and `fromSpecStalk_app` directly. Loogle did not
   recognize the unqualified short-complex identifier; local Mathlib contains
   it under CategoryTheory. No existing theorem eliminates either compatibility
   argument. `ResolutionSectionScalarMap` concerns restricted resolutions and
   cohomology of multiplication morphisms, and still has a hole; it is not a
   shorter proved replacement. The sole public import is needed for the theorem's
   signature. Both old dependency nodes remain used, so `No longer needed` is
   complete. Read `dag/units/sk-thm-p1.json`: this scalar lemma realizes none of
   its fixed statement/steps; this change is below that route and bypasses none.
5. **DAG: pass.** Compared the node JSON with the repository. Only `proof` and
   `proof_origin` changed; the statement, dependencies and Lean record did not.
   The union of step `uses` equals `proof_deps`. The class-map node supplies the
   actual construction, while the exact-functor Mathlib leaf supplies the
   homology comparisons. The rewritten steps describe the two private proofs,
   including the simplification avoiding an identification of the open with top.

Second reading changed only this report by adding the independent review and
validation evidence. No Lean or node repair was needed. Holes closed: one,
`AlgebraicGeometry.localDirectImage_stalk_class_smul`; holes added: zero;
split off: zero; imports/modules pruned: none.

Delivery validation: `deliver3.py --no-push` printed OK and passed preflight
(review class CODEX because the node proof changed). The tool's exhaustive axiom
probe timed out at 60 seconds; it reports that the merge runs the probe again.
The independent explicit `#print axioms` scratch compilation above completed in
48.8 seconds and checked every proof declaration added or completed in this file.
