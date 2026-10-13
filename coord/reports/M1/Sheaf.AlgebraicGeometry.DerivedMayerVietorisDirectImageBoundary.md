## What changed

Replaced the rejected restatement reduction with a real composition proof in
`schemeMV_directImage_boundary`. The proof uses Mathlib connecting-map naturality,
the landed direct-image split-triangle theorem, and two strictly smaller intermediate
statements: the K-injective shift comparison and the fixed-resolution Mayer–Vietoris
comparison. Added the two corresponding modules and DAG nodes.

## Proved and sorry left

`schemeMV_directImage_boundary` is proved. The new declarations
`derivedModuleDirectImageKInjectiveIso_shift` and
`schemeMV_image_resolution_comparison` remain as named, strictly smaller obligations.

## No longer needed

The prior `DerivedMayerVietorisDirectImageBoundaryNaturality` restatement module was
removed. No proof dependency from the original plan is imported unless used by the
three delivered modules.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced an intermediate theorem with exactly the target
statement, which `deliver3.py` correctly rejected as a restatement. The repaired
intermediates split the shift compatibility and the concrete resolution comparison,
then combine them with `triangleOfSESδ_naturality`.

## New nodes

`lem-pc-direct-image-kinjective-comparison-shift` records the shift-compatibility
obligation. `lem-pc-mayer-vietoris-image-resolution-comparison` records the map of
concrete short complexes. Both node files are in `dag/nodes/sec-picard-framework/`.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and the target proof is a genuine composition using
`triangleOfSESδ_naturality`. The two new declarations have strictly smaller conclusions:
one isolates shift compatibility and one constructs the map of concrete short complexes.
Their hypotheses match the fixed resolution data used by the target, and both modules
compile in import order with the item.

## Second reading by M1

1. **Statements and signatures.** Compared the delivered boundary module with the repository version:
   `schemeMV_directImage_boundary` is unchanged byte for byte. The two added declarations are strictly
   smaller reductions, not restatements. Verdict: pass.
2. **Proof and axioms.** Compiled all delivered modules in import order with `lcompile.py`; the boundary
   proof is error-free. The only remaining `sorry`s are the two named split-off declarations, with no
   sorry in a definition and no forbidden axioms or commands. Verdict: pass.
3. **Split-off statements.** Checked both new statements against their docstrings and DAG nodes. They are
   true obligations from the source construction, weaker than the target, and used by its proof. Verdict:
   pass.
4. **Pruning and route.** The proof uses the direct-image split-triangle theorem, shift comparison, and
   connecting-map naturality. The rejected restatement module is absent and no unused old dependency is
   imported. Verdict: pass.
5. **DAG agreement.** The two new node records match their declarations, modules, proof origins, and split
   status; the target node statement remains unchanged. Verdict: pass.

Changed only the boundary proof, added the concrete comparison module and node, and retained the required
shift-comparison module and node. No statement or definition was changed.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and the target proof is a genuine composition using
`triangleOfSESδ_naturality`. The two new declarations have strictly smaller conclusions:
one isolates shift compatibility and one constructs the map of concrete short complexes.
Their hypotheses match the fixed resolution data used by the target, and both modules
compile in import order with the item.
