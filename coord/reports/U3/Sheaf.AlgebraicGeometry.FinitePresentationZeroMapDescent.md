## What changed

Replaced the sorry in `AlgebraicGeometry.finitePresentation_zero_map_descent` by a
complete Lean proof from vanishing on a single fixed affine open. The proof uses
quasi-compactness over the affine base to construct the finite affine subcover,
chooses one directed upper bound for its stages, and proves global vanishing by
naturality and separatedness of the target sheaf on intersections with arbitrary
opens. The signature and existing docstrings stay unchanged.

Added proof-only imports of `Mathlib.Data.Finset.Order`,
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`, and
`Sheaf.AlgebraicGeometry.FinitePresentationZeroMapAffineOpen`.
Updated the existing node's proof and dependencies to follow this Lean argument.
No statement, definition, visibility, or public import was changed.

Both modules compile cleanly with `lcompile.py --all`, in under ten seconds each.
The new statement was checked against the affine argument of Stacks Tag 01ZR (3),
first proof, and its linked Algebra Tag 05N7. The local literature checkout lacks
`limits.tex`, so the authoritative Stacks page was read directly:
https://stacks.math.columbia.edu/tag/01ZR .

## Proved and sorry left

Closed: `AlgebraicGeometry.finitePresentation_zero_map_descent`
(node `lem-pc-fp-zero-map-descent`). Its proof has no sorry.

Added and left: `AlgebraicGeometry.finitePresentation_zero_map_affine_open_eventually`
(node `lem-pc-fp-zero-map-affine-open-eventually`), in the new module
`Sheaf.AlgebraicGeometry.FinitePresentationZeroMapAffineOpen`.
Its entire proof is `by sorry`. This is the affine-chart part of the argument,
not the global conclusion under another name: it assumes no quasi-compactness
of the model and only concludes vanishing on subopens of one fixed affine chart.
The original module now performs the finite-cover and directed-stage gluing itself.
One upper hole closed and one lower hole added: decomposition, net zero holes,
not a sorry-free proof of the mathematical theorem.

Edge cases checked mathematically: empty affine open, empty scheme (empty finite
cover), zero source, zero target, singleton index preorder, and non-antisymmetric
directed preorders. No nonemptiness hypothesis on I is added: the supplied j gives
Nonempty I locally. Finiteness of the target's presentation is used only in the
remaining affine argument. No affine intersection hypothesis is needed: intersections
are used merely as opens for the target sheaf's separatedness.

## No longer needed

No imports removed and no modules or nodes pruned. The original item did not import
its two planned Mathlib-leaf dependencies. The global proof no longer uses
`lem-weil-pbc-spec-colimit-limit` or
`lem-pc-filtered-colimit-commrings-elementwise` directly; both are retained in the
new affine-open node's proof dependencies. They are still needed transitively and
must not be counted as pruning. The finite affine cover, common upper bound, and
sheaf-separatedness steps require no new sorry-bearing modules.

## Where the brief, the DAG or earlier work was wrong

The existing plan labels the affine restriction/finite-generation step elementary,
but its formalization requires the affine sections comparison and the affine
finite type criterion. The new affine-open node records
`lem-weil-pbc-module-pullback-affine-sections` and
`lem-weil-pbc-quasi-coherent-finite-type-affine` for this purpose, and the tensor
pullback composition node for persistence. Their statements were read; the ring-level
`FinitePresentationColimit` theorem alone does not supply this scheme transport.

Searches: LeanFinder returned structure-sheaf eventual-zero results; Loogle verified
`Scheme.Modules.Hom.app` and the structure-sheaf section theorem. Grep found no
matching module-map descent theorem. LeanSearch returned an HTTP Internal Server
Error and is recorded as unavailable, not as a negative search. Searches in the
source library and the DAG found no existing affine-open version. Blueprint searches
for `vanishing affine` and `01ZR` had no matches; `zero map` returned six unrelated
definitions. The item's existing blueprint ancestor is retained.

The unit record `sk-thm-picard-semicon` has empty `realized` lists; this decomposition
stays inside the existing node's affine/local-to-global route and bypasses no unit.
The existing node's two Mathlib leaves remain lower proof tools.

## New nodes

`lem-pc-fp-zero-map-affine-open-eventually` is the affine-local portion of the
original argument, without quasi-compactness of f. It concludes vanishing on every
subopen of one chart at every sufficiently late stage. Its module is
`lean/Sheaf/AlgebraicGeometry/FinitePresentationZeroMapAffineOpen.lean`; its node is
`dag/nodes/sec-picard-framework/lem-pc-fp-zero-map-affine-open-eventually.json`.
The complete proof in words explains the affine ring colimit, finite generators,
finite-matrix relation witnesses, lifting coefficients, eventual vanishing of the
finite differences, and persistence under tensor pullback. No change record is
needed: all existing interfaces are unchanged.

## Second reading by U3

1. Compared the delivered module with the repository version. The theorem signature and existing declarations are unchanged; only proof-only imports and the proof body differ. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`; they compile without errors. The descent theorem has no `sorry`; the affine-local theorem is the named split-off hole. No forbidden declarations occur. Verdict: pass.
3. Checked the affine-local split statement against its documented affine finite-presentation argument and DAG node; it is a strict local reduction and has the required source, proof description, and node. Verdict: pass.
4. The descent proof follows the finite affine-cover, directed upper-bound, and sheaf-separatedness route, and retains the unit route. Verdict: pass.
5. DAG proof, proof dependencies, and proof origin match the imports and theorem calls used by the proof. Verdict: pass.

Changed only the report metadata while reviewing; no Lean proof changes were needed.
