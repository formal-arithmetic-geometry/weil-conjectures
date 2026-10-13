## What changed

Proved `ModuleCat.exists_projective_presentation_kernel_projection_data` in
`Sheaf.RingTheory.WellOrderedPresentationKernelProjectionData` from a new, strictly earlier
construction theorem in `Sheaf.RingTheory.WellOrderedPresentationComponentData`.
The existing statement, visibility, and public imports are unchanged. Added proof-only imports
of the component-data module and `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

The main proof constructs the short exact kernel complex of the surjection, proves the
predecessor-supremum pullback identity (including empty predecessor sets), constructs the
linear augmentation-kernel projection, proves its surjectivity by lifting and subtracting a
predecessor vector, identifies its kernel, and transports it to the categorical kernel.
Updated the parent node's proof and dependencies to this route. No definitions or existing
interfaces changed; no forced adaptations or change records are needed.

## Proved and sorry left

Closed the original hole in `ModuleCat.exists_projective_presentation_kernel_projection_data`
(node `lem-weil-pbc-well-ordered-presentation-kernel-projection-data`). The proved private
helper `predecessor_comap` uses only Mathlib and handles both nonempty and empty predecessors.
There are no remaining holes in the assigned module.

Added one hole: `ModuleCat.exists_projective_presentation_component_data`
(node `lem-weil-pbc-well-ordered-presentation-component-data`), the construction of the
projective middle module, its filtration, stage-image equalities, and ordinary component
maps. Its proof is exactly `by sorry`, with source and complete construction in its docstring.
It makes no assertion about the kernel of the presentation map or about any map from that
kernel. This is a decomposition: one upper hole closed and one strictly earlier hole added,
net zero holes. It is not a sorry-free proof of the original theorem.

Both delivery modules compile through `lcompile.py --all`; the main module has no warnings.
Edge cases checked against the construction: the cover excludes empty E; zero M has no
active indices and permits B=0; repeated stages are inactive; at a least active stage the
predecessor supremum is zero. No arbitrary witness is used as the data of any definition.

## No longer needed

No existing import was removed, and no module is globally pruned by this decomposition.
The parent's direct use of `def-weil-pbc-direct-sum-modules` and
`def-weil-pbc-finite-global-dimension` is replaced by the new component-data node; both
remain needed inside that construction and are not claimed as globally pruned.
The unit's realized statement and proof steps are unaffected.

## Where the brief, the DAG or earlier work was wrong

The four existing proof dependencies of the assigned node provide definitions, not the
filtered direct-sum construction. Their declarations alone do not implement that step.
The delivery isolates it in one new theorem, and proves the entire subsequent kernel
argument. The shorter-route searches found only resolution and lattice infrastructure.
No statement correction or mathematical dispute was needed. The cited Stacks source was
read at https://stacks.math.columbia.edu/tag/0D1U because this clone has literature lists but
not the regenerated algebra.tex. The adaptation to supplied categorical projectives and
arbitrary index universes is the explicit construction already described in the parent node.

## New nodes

`lem-weil-pbc-well-ordered-presentation-component-data`, module
`Sheaf.RingTheory.WellOrderedPresentationComponentData`, declaration
`ModuleCat.exists_projective_presentation_component_data`: the direct-sum presentation
construction before intersecting with its kernel. It records the active-index size reduction,
categorical projectivity, well-founded image induction, finite-support component-kernel
identity, and the augmentation commuting square. The source, three kinds of searches, full
proof plan, and Lean signature are recorded in its node. No change record is needed.


## Second reading by E3

1. Interface preservation: PASS. Compared both delivered modules with the repository.
   The component module is new; the existing kernel-projection theorem's signature is
   byte-for-byte unchanged. Its existing docstring and public imports are unchanged.
   Only proof imports, a private helper, and the theorem proof were added. There are
   no changed definitions, existing statements, forced adaptations, or change records.
2. Proof and axioms: PASS as a decomposition. Compiled both files locally in import
   order without errors or warnings. Scratch-copy `#print axioms` reports
   `propext`, `Classical.choice`, `Quot.sound` for `predecessor_comap`; the main
   theorem additionally reports `sorryAx` from the component theorem. The component
   theorem reports the same three standard axioms plus `sorryAx`. No forbidden declarations or hollow definitions
   occur. The only remaining hole is the named component construction listed above.
3. Split statement: PASS. Matched every hypothesis and conclusion against its node:
   arbitrary ring and index universes, supplied resolutions, projective B, exhaustive
   monotone H, stage-image equalities, predecessor alternative, surjective component
   p with prescribed kernel, and both commuting identities. The docstring supplies
   the full active-index/direct-sum construction. This is strictly the construction
   before intersecting with ker b, not a renamed kernel-projection theorem. Checked
   empty E (hcover at zero makes it impossible), M=0 (B=0, all stages inactive),
   repeated stages (no new summand), and least active stage (predecessor zero).
   The active indices inject into M, so shrinking them to universe v is valid even
   when w is larger. Projectivity is categorical in universe v throughout.
   Independently read Stacks 0D1U and its direct-sum induction argument. Searches
   with `projective module transfinite filtration direct sum presentation component
   projection` (LeanFinder), `Submodule.comap, iSup` (Loogle), and `filtered
   projective presentation|component projection|predecessor supremum` (grep), plus
   rg of the project and Mathlib, found infrastructure rather than this construction.
   In particular `Submodule.comap_iSup_map_of_injective` applies to images under
   the injective map, not the arbitrary predecessor family here. No short closure
   of the component construction was found.
4. Route and pruning: PASS. Read the proof downward from the original theorem.
   It obtains component data, constructs the genuine short exact kernel complex,
   proves the predecessor pullback identity including its empty case, then lifts
   an augmentation-kernel vector and subtracts a predecessor vector. This proves
   surjectivity; the prescribed component kernel identifies the new kernel, and
   `ModuleCat.kernelIsoKer` transports to the required categorical kernel. Both
   added imports are proof-only and used. Existing public imports support the
   signature and remain. All four old proof dependencies are accounted for:
   exact-sequence and quotient-module remain direct; direct-sum-modules and
   finite-global-dimension move into the component construction, as recorded
   under No longer needed. No module is pruned. Read sk-thm-p1's realized statement
   and all realized steps: this change stays below them and bypasses none.
5. Node agreement: PASS. Existing node changes are exactly proof, proof_deps, and
   proof_origin; the uses union equals proof_deps. The new node records its source,
   full construction, searches, creation metadata, parent blueprint route, chapter,
   unit, and verbatim Lean statement. Its data matches the delivered theorem.

Second-reading changes: added the missing blueprint marker to the new module's
module docstring and this point-by-point review. No proof repair was needed.
One original hole closed and one strictly earlier hole added: net zero, a
one-hole decomposition rather than a completed axiom-free proof of the item.
