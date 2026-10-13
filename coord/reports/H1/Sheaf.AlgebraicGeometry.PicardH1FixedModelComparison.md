## What changed

Reduced `AlgebraicGeometry.Scheme.picard_h1_fixed_model_comparison` to fixed-affine
target normalization and residue comparison of chain representatives. Its public
signature and existing docstring are unchanged. The two new proof-only imports carry
those geometric steps. The existing free-sections equivalence evaluates the strictly
perfect retracts. A proved private helper, `joint_free_coordinates`, enumerates their
finite coordinates; the main proof verifies the section retract equations and
constructs `b` and the product projection `rho`, with `rho.comp b = t`.
Beta is the supplied product residue map composed with the base change of `rho`.
`LinearMap.baseChange_comp` and the residue comparison prove the final square.

## Proved and sorry left

The original body hole of
`AlgebraicGeometry.Scheme.picard_h1_fixed_model_comparison`
(lem-sc-picard-h1-fixed-model-comparison) is replaced by a complete written combination.
This is a decomposition: one upper hole is replaced by two strictly smaller geometric
holes, rather than a sorry-free proof of the entire import closure.

Added exactly two whole-proof holes:

- `AlgebraicGeometry.Scheme.picard_affine_target_normalization`
  (lem-sc-picard-affine-target-normalization): a normalized target for a single
  morphism and module on the already supplied affine. No source model or square.

- `AlgebraicGeometry.Scheme.picard_fixed_model_residue_chain_comparison`
  (lem-sc-picard-fixed-model-residue-chain-comparison): for supplied normalized
  targets, an evaluated product section map and its product residue comparison.
  No finite free ambient target, rank q, or joint free map b.

There is no textual sorry in the item's module, no new data definition, and no
arbitrary witness of unproved existence chosen in a definition. The construction
works without separate branches for n=0 and m=0. The earlier attempt recorded
successful section-projection checkpoints and a complete item compile. The
reproduced set compiled all three modules successfully. The one line-length
warning introduced while correcting the new lemma docstring was fixed before the
final no-push dry run. Runner wall times include waits for shared compilation slots;
each successful Lean invocation stays within the tool's 60-second limit.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit`
- `Mathlib.RingTheory.LocalRing.Module`
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
- `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`
- `Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
- `Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial`

Their geometric facts remain needed in the two new nodes' proof plans. No module is
claimed globally pruned. The item's proof dependencies are now the two new nodes and
`def-pc-perfect-complex`. Old direct proof edges to
`lem-pc-rf-perfect-base-change`, `lem-pc-module-pullback-adjunction`,
`lem-pc-perfect-affine-map-representative`, `lem-pc-perfect-affine-bounded-projective`,
`lem-pc-affine-localized-derived-sheafification`, `lem-sc-flat-derived-structure-unit`,
`lem-sc-field-pullback-rank-one-trivial`, `lem-pc-cohomology-sections-affine-base`,
`def-sc-derived-fiber-betti`, `def-sc-structure-sheaf-cohomology-pullback`, and
`def-weil-residue-field` are replaced by appropriate edges of the new nodes.
The public statement imports remain unchanged. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first reproduced dry run compiled the set and passed its axiom probes, then
reported that any new attribute command requires a change record. The record for
local proof elaboration is supplied. The second-reading section is intentionally
left to the next worker as instructed.

The earlier residue lemma proof claimed that the ratio of target fibre
trivializations is a scalar, although it does not assume the target universal
H-zero units. This is unnecessary: use the pullback of the chosen source fibre
trivialization directly for each target cohomology identification. The new lemma
docstring and proof node now give this compatible choice, which makes the
coefficient pullback the canonical structure-module pullback without comparing
scalars. No Lean statement changes.

The planned declarations do not expose fixed-affine normalization or the canonical
residue square. A model after shrinking U does not meet the supplied-affine statement.
The new lemmas isolate those geometric steps of the existing plan. Stacks Tag 0BF2,
the displayed chain maps before H-one injectivity, was read directly. The fixed-affine
finite-projective adaptation is the argument already recorded in the original node.

Existing searches in searches.jsonl used LeanFinder, Loogle, logged Mathlib grep,
and repository rg; LeanSearch returned Internal Server Error. No exact existing
geometric comparison or duplicate blueprint node was found. The elementary finite
coordinate enumeration and tensor composition use existing Mathlib lemmas directly.
Both new nodes preserve the explicit ancestry to `thm-sc-theorem-of-cube`.

Edge cases: empty index sets give q=0 and unique product maps. Zero source rank gives
zero source H-one by minimality. Target normalization allows an empty affine; the
residue statement assumes w in U. No reducedness assumption is used in the global
projective splitting argument.

The previous attempt repeatedly exceeded the 60-second compile limit. This repair
keeps all proved helpers in the item's file. An attempted extra helper module was
removed to comply with the prohibition on splitting files to evade that limit.
The final residue interface bundles the section and cohomology maps into products;
this avoids reconstructing dependent cohomology group instances in the main proof.
The unchanged target signature was compared textually with the repository.

## New nodes

`lem-sc-picard-affine-target-normalization`, in
`Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization`, carries the fixed-affine
connective projective normalization step. Its docstring gives negative cancellation,
unit splitting, and remaining degree-zero cancellation over nonreduced bases.

`lem-sc-picard-fixed-model-residue-chain-comparison`, in
`Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison`, carries chain
representation, source residue minimality, source fibre triviality, target-cycle
projection, compatible source-induced fibre trivializations, and base-change
naturality. Coordinate projections and products assemble the individual residue comparisons into its stated product map.

Both nodes belong to sec-abelian-varieties / sk-prop-av-cube. No existing interface was
changed. The static preflight requires a record for the local irreducibility
command: `coord/changes/picard-h1-fixed-model-local-elaboration.md` documents its
scope, the unchanged signature, and all downstream users. No forced adaptation is
required. Nothing is pushed.

## Second reading by H1

1. I diffed `PicardH1FixedModelComparison.lean` against the repository version. The public theorem signature and existing declarations are unchanged byte for byte; only proof imports, private proof helpers, and the proof body changed. The two added modules and their DAG nodes are new split-off declarations, with no accidental edits to repository files.

2. I compiled the three sandbox modules with `lcompile.py`; the affine normalization, residue-chain comparison, and main comparison modules all elaborate successfully. The item's file has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The two split-off theorems contain the only remaining proof holes, each named and documented, and their declarations are the only new `sorry` sites. The main theorem's generated proof uses only the permitted classical constructions together with imported open statements.

3. I checked both new statements against their implementations and DAG records. They are strictly smaller than the main target: the normalization lemma supplies a fixed-affine target model, while the residue lemma supplies evaluated chain and residue maps without the finite-free ambient target or joint map. Their docstrings, sources, proof steps, `proof_deps`, and declarations agree. The edge cases of empty index sets and zero source rank are handled by the product and finite-coordinate constructions; no arbitrary witness is introduced in a definition.

4. I checked the proof route and pruning. The main proof uses exactly the two new geometric lemmas and `def-pc-perfect-complex`; removed direct proof-only imports are listed in `## No longer needed`, and the public imports remain appropriate. The finite-coordinate helper is elementary and does not bypass the unit route. The unit's realized route remains recorded in the DAG.

5. I checked the DAG nodes and metadata. The main node records the two new proof dependencies and the finite-free construction, while each split node has source, proof plan, searches, ancestry, chapter, unit, and Lean declaration metadata. No duplicate existing declaration was found by repository search or the recorded searches.

I changed only this second-reading report section; no Lean proof or statement required repair.
