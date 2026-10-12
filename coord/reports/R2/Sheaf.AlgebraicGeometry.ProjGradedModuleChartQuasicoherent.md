## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.ProjGradedModuleChartQuasicoherent`
with a compiling reduction. Its existing theorem signature and docstring are unchanged.
The proof obtains the affine tilde comparisons, transfers quasi-coherence from tilde through
restriction along `basicOpenIsoSpec`, proves that the positive homogeneous standard opens
cover Proj by reindexing Mathlib's `affineOpenCover`, and applies
`SheafOfModules.IsQuasicoherent.of_coversTop`.

Two private, fully proved helpers implement quasi-coherence transport: `chartOverQuasicoherent`
uses the inverse of `Scheme.Modules.overEquiv`, its unit comparison and the equivalence unit;
`quasicoherent_of_tildeChart` uses Mathlib's tilde and open-restriction instances. Explicit
scheme and ring arguments prevent expensive elaboration of the concrete Proj chart.

Added `Sheaf.AlgebraicGeometry.ProjGradedModuleChartTildeComparison`, containing the remaining
single-chart isomorphism obligation, with a detailed source-based proof in its docstring.
Updated the original node's proof, proof dependencies and proof origin, and added the matching
node. Only private proof imports changed in the existing module. No definitions, public
imports or existing signatures changed; no other existing module was adapted.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Proj.gradedModuleChart_quasicoherent`
(node `lem-weil-pbc-proj-graded-module-chart-quasicoherent`) by decomposition, not by a complete
sorry-free proof. There are no holes in the item module.

Added exactly one hole: `AlgebraicGeometry.Proj.gradedModuleChart_tildeComparison`
in `Sheaf.AlgebraicGeometry.ProjGradedModuleChartTildeComparison`, node
`lem-weil-pbc-proj-graded-module-chart-tilde-comparison`. It asserts the isomorphism on each
individual affine chart, with its specified module `Z f`; it does not assert global
quasi-coherence. This isolates original proof steps 1--3. The transfer, cover and locality
step is fully proved in the item. Net hole reduction: zero (one closed, one added).
No other holes were added or changed.

The two modules compile together through `lcompile.py --all`. The original theorem still
transitively depends on the new hole. The only new data-bearing expressions are local choices
of isomorphisms inside proofs of propositions; no definition chooses data from existence.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.Algebra.Module.GradedModuleAwayRestriction`: its comparison is needed inside the
  new affine-comparison obligation, and remains a proof dependency of that new node.
- `Sheaf.Topology.SheafOfModulesFromBasis`: basis uniqueness is needed inside the new
  affine-comparison obligation, and remains a proof dependency of that new node.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: redundant as a direct import because the new
  comparison module publicly imports it for its statement.

No mathematical node or module is claimed permanently pruned. In particular the original
algebraic restriction, basic-open intersection, basis-extension, and tilde-section nodes
remain needed, directly or through the new node. No unit-level statement or step is bypassed.
The three existing public imports of the item are unchanged.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not directly state the isomorphism of an arbitrary chart-compatible
sheaf with the affine tilde sheaf. `gradedModuleAwayRestriction` supplies the algebraic
localization comparisons, and `exists_sheafOfModules_from_basis` supplies a universal property;
constructing compatible linear comparisons on the transported principal basis is additional
glue. This is the new obligation, with the original argument retained in full.

Read the local Stacks source, `constructions.tex`, labels `lemma-standard-open`,
`lemma-proj-sheaves`, `lemma-standard-open-proj` and `lemma-proj-scheme`. The last paragraph of
`lemma-proj-scheme` explicitly states the affine tilde comparison used here. The source files
are absent from this read-only clone but available in the local literature copy. LeanSearch
returned Internal Server Error; recorded as unavailable, not as evidence of no match.
LeanFinder and local Mathlib/library searches found the ring charts, tilde, restriction and
locality tools but no graded-module sheaf comparison theorem.

Checked the new statement's empty-chart and empty-Proj cases, r=0, nilpotent denominators,
zero modules, degree greater than one, and degree-zero numerators. In the principal-open
argument h=f*a has degree (n+1)*deg(f)>0; its localization element is r^deg(f), so positive
powers give the same localization without any degree-one generation hypothesis.

The blueprint ancestor helper returns None because the existing node's creation chain uses
module names. The new node follows the recorded ancestor of the extension node,
`lem-weil-pbc-symmetric-product-finite`, with the intervening chain made explicit.

## New nodes

`lem-weil-pbc-proj-graded-module-chart-tilde-comparison` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-proj-graded-module-chart-tilde-comparison.json`:
the affine tilde comparison of original steps 1--3, stated by
`AlgebraicGeometry.Proj.gradedModuleChart_tildeComparison` in the new module
`lean/Sheaf/AlgebraicGeometry/ProjGradedModuleChartTildeComparison.lean`. Its proof records
principal-open realization, uniqueness of the given restriction maps, compatible localized
section comparisons, and extension of the basis isomorphism. Searches are recorded in
`searches.jsonl`; no existing statement with this conclusion was found. No change record is
needed: the existing interface is unchanged.

## Second reading by R2

1. Compared both delivered modules with the repository. The existing theorem signature and
   all existing declaration signatures are unchanged; the new theorem is a strictly smaller
   affine-chart comparison and has a matching node.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds. The only remaining
   `sorry` is the named theorem `gradedModuleChart_tildeComparison`; no definitions contain
   `sorry`, and the delivery introduces no forbidden declarations. The proof uses only the
   imported comparison hole plus ordinary propositions; the maintainer probe is deferred to
   delivery preflight.
3. Read the new statement and checked edge cases recorded by the worker: zero and nilpotent
   denominators, empty charts and empty Proj, zero modules, and arbitrary positive degrees.
   The conclusion is exactly the single-chart isomorphism needed by the parent and is weaker
   than global quasi-coherence. Its docstring gives the source and a complete proof plan.
4. Checked the proof route against the DAG and unit. The parent uses the new comparison, then
   the Mathlib tilde quasi-coherence instance, affine-chart transport, the positive homogeneous
   affine cover, and locality. The new module now retains private imports of graded-module
   restriction and basis-extension, matching its node's proof dependencies; no unnecessary
   public import was added.
5. Checked node metadata and report accounting. The parent node's `proof`, `proof_deps`, and
   `proof_origin` follow the Lean proof; the split node records its source, dependencies,
   searches, and declaration. The decomposition closes one hole and adds one strictly simpler
   hole, with no hollow definition or accidental statement change.

Changed during second reading: restored the two private proof imports in the new comparison
module so its implementation and DAG dependencies agree, and added this review section.
