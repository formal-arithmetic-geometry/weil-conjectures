## What changed

Proved `AlgebraicGeometry.eventually_affine` in
`lean/Sheaf/AlgebraicGeometry/EventuallyAffine.lean`, with its signature and existing
public import unchanged. The proof follows Stacks 09ZM using Mathlib directly:
a finite affine cover of the base, restricted limiting cones on `Over b`,
`Scheme.exists_isAffine_of_isLimit`, a common finite upper bound, and
`HasAffineProperty.of_iSup_eq_top`. Updated the node proof and proof dependencies
so they match the actual argument. No new declaration, module, or import.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.eventually_affine`
(node `lem-weil-pbc-eventually-affine`). No holes remain in the delivered module;
no holes were added or split off. This is a proof using Mathlib, not a decomposition.
Local compilation passed without errors or warnings. The delivery dry run also
checks every declaration's axioms and performs the server compilation.

The empty base/empty finite cover is handled by `IsCofiltered.inf_objs_exists`
on the empty finite set and the vacuous affine-cover criterion. The proof only
uses a preorder; it does not require antisymmetry. Every later index is handled
by the arrow associated to its inequality with the selected index.

## No longer needed

Removed imports: none. The sole existing public import
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` is needed.

Removed proof dependencies:
- `lem-weil-pbc-open-preimage-fibre-product`: no base-change description of the
  structure map's restriction is needed.
- `lem-weil-pbc-qcqs-over-affine`: compactness follows directly from compact
  preimages and quasi-separatedness from the open-subspace criterion.

No Sheaf or WeilConjectures module is needed as an additional proof import.
All remaining geometric dependencies have existing Mathlib realizations.
These pruning claims concern this proof; other users may still need those nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG's base-change detour to verify qcqs of the restricted stages is unnecessary.
Mathlib's compact-preimage and quasi-separated open-subspace API proves exactly
these hypotheses directly. The finite-cover, restricted-limit, absolute-affine-stage,
and local-on-target route is kept. No statement or definition was changed.

## Second reading by U3

1. **Visible declarations unchanged — pass.** Diffed the sole delivered module
   against the repository. Everything before the original `:= by`, including
   imports, docstrings and the complete signature, is byte for byte unchanged.
   The preorder, directedness, nonempty index, qcqs base and stages, affine
   transitions, limiting cone, compatibility and affine limit-map assumptions
   match the node and Stacks Limits Lemma 09ZM (limits.tex, lines 891–911).
   The conclusion still covers every index above the chosen index. No definition
   or statement changed; no change record is required.

2. **Proof and trust — pass.** Independently compiled the module through
   `lcompile.py`: no errors or warnings. Scanned the delivered Lean for `sorry`,
   axioms and prohibited implementation mechanisms: none occur. Compiled a
   scratch copy with `#print axioms AlgebraicGeometry.eventually_affine`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   This closes one hole and adds zero, rather than decomposing the theorem.

3. **Split statements — pass (none).** There are no new declarations, nodes,
   modules or split-off holes to check. Read the actual Mathlib signatures and
   proofs of `opensDiagram`, `opensCone`, `isLimitOpensCone`, its affine-transition
   instance, and `Scheme.exists_isAffine_of_isLimit`. The latter receives a
   cofiltered `Over b` diagram of compact, quasi-separated schemes. Compactness
   comes from quasi-compact preimages of the compact affine open; the initial
   structure map is quasi-compact because its source is compact and its target
   quasi-separated. Quasi-separatedness passes to each open subspace.
   Compatibility identifies the limiting open with the affine preimage under
   `f`; naturality identifies each selected stage with its structure-map preimage.

4. **Shortest route, imports and pruning — pass.** Searched Mathlib's
   algebraic-geometry sources and both library roots for eventual-affineness
   statements and read nearby finite-cover descent lemmas. No existing theorem
   directly proves this relative conclusion; the proof uses the absolute
   affine-stage theorem directly. For each later index, the preorder arrow and
   the finite common-bound arrows give an affine transition to each chosen
   stage, so its preimage is affine. `HasAffineProperty.of_iSup_eq_top` then
   proves affineness of the structure map. Read `inf_objs_exists`: its empty
   finite-set branch chooses an object using cofiltered nonemptiness, so an
   empty affine cover is supported without an extra hypothesis. Antisymmetry
   is never needed. The single public import supplies the public signature and
   the proof; no proof-only public import was added. The report lists both and
   all removed old proof dependencies. Checked the `realized` records of the
   units, including `sk-thm-p1`: neither removed node is a realized statement or
   step, and the unit route is unchanged. No module import was pruned.

5. **DAG agrees — pass.** Compared the delivered node with the repository:
   only `proof`, `proof_deps`, and `proof_origin` differ. Checked that
   `proof_deps` is exactly the union of the steps' `uses`. The finite affine
   cover, direct qcqs check, restricted limiting cone, absolute affine-stage
   theorem, common bound and local-on-target criterion match the Lean proof.
   Read the dependencies' Mathlib matches; all retained geometric steps have
   existing Mathlib realizations. The node statement and Lean record are
   unchanged. No new-node fields are required.

Second reading changed only this report by adding the independent review.
The Lean proof and node metadata required no repair. The source proof's phrase
“a finite morphism is affine” is an irrelevant wording slip: its hypothesis
already says the limit morphism is affine, which is precisely what Lean uses.
