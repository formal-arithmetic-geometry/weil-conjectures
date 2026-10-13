## What changed

`relativeMV_boundary_completion` now constructs both boundaries using Mathlib's
`DerivedCategory.triangleOfSESδ`, proves distinguishedness by explicit triangle
isomorphisms, and proves the connecting square by SES boundary naturality and
the first and overlap component identities. The geometric complex-level
construction is isolated in `RelativeMVSESPresentation`.
No signature or definition changed. No data definition chooses an arbitrary
existence witness; all presentation witnesses are eliminated inside the proof.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.relativeMV_boundary_completion`.
Added one hole: `AlgebraicGeometry.relativeMV_ses_presentation`
(node `lem-pc-relative-mv-ses-presentation`). This is a decomposition, net zero
holes: the remaining statement supplies short exact complexes and comparisons;
it asserts neither a boundary equation nor distinguishedness. The passage from
that construction to both distinguished triangles and their compatible boundaries
is complete Lean in the assigned module.

## No longer needed

The assigned module replaces its private proof import
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` with
`Sheaf.AlgebraicGeometry.RelativeMVSESPresentation`. The former module remains
imported privately by the new presentation module: this is a moved dependency,
not a claim of global pruning. No module is claimed globally unnecessary.

Every old direct `proof_deps` entry is absent from the completed boundary node:

- `def-pc-derived-base-change-map`
- `def-pc-derived-open-restriction-maps`
- `def-pc-derived-pullback`
- `def-pc-relative-mv-maps`
- `lem-pc-derived-direct-image-preserves-qcoh`
- `lem-pc-derived-mayer-vietoris-functorial`
- `lem-pc-derived-mayer-vietoris-triangle`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pc-ringed-spaces-derived-adjoint`
- `lem-pc-ringed-spaces-derived-pullback-composition`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-weil-pbc-morphism-affine-schemes-affine`
- `lem-weil-pbc-qcqs-over-affine`

All these nodes are retained in the new presentation node's proof plan. Its
non-Mathlib proof dependencies now have direct imports, privately unless needed
by the statement. The geometric argument has not been discarded.

## Where the brief, the DAG or earlier work was wrong

The compiled `RelativeMVMaps` dependency was temporarily absent, then appeared
on the next library refresh. An exploratory lemma claiming naturality for
arbitrary boundaries was rejected and removed; it is not in the delivery.
The construction must keep the two short exact diagrams and their morphism
together. The single-cover theorem alone does not supply this compatibility.
The local Stacks source file was absent; the three tagged primary-source pages
were read on the Stacks website: [08BV](https://stacks.math.columbia.edu/tag/08BV),
[08HZ](https://stacks.math.columbia.edu/tag/08HZ), and
[08HY](https://stacks.math.columbia.edu/tag/08HY). The mapping-cylinder presentation of the image
diagram is a further complex-level construction required by the new node;
this remains for the next worker, alongside the pinned mates comparisons.

## New nodes

`lem-pc-relative-mv-ses-presentation`: a complex-level geometric comparison prior
to the triangulated passage. Empty opens and zero complexes yield zero complexes;
repeated opens yield split sequences. No invertibility of any base-change map is
required. The theorem is stronger chain-level data, used only for the source
proof route; its boundary consequences are proved here, not assumed.

## Second reading by W4

1. Compared the existing module with the repository using `diff -u`, and
   checked the theorem signature byte for byte. Verdict: unchanged statement,
   hypotheses, visibility and definitions; only the private proof import and
   proof body changed. The new module has no data definition or chosen witness.
2. Compiled both delivered modules locally in import order with lcompile.py.
   Verdict: clean compilation. The only delivered sorry is the named
   `AlgebraicGeometry.relativeMV_ses_presentation`. The explicit boundary proof
   transports Mathlib's SES boundaries, constructs both triangle isomorphisms,
   and uses SES naturality; it does not assume the boundary equation.
   Scratch-copy #print axioms checks for both declarations returned exactly
   propext, Classical.choice, Quot.sound and sorryAx. The latter is expected
   from the open presentation and upstream holes; this is not an axiom-free
   completion. No axiom, unsafe, opaque, extern or implemented_by declaration
   is present.
3. Read the presentation theorem, its docstring and matching node against
   [08BV](https://stacks.math.columbia.edu/tag/08BV),
   [08HZ](https://stacks.math.columbia.edu/tag/08HZ) and
   [08HY](https://stacks.math.columbia.edu/tag/08HY). Verdict: a geometric
   complex-diagram subproblem, not a renamed boundary-completion statement.
   Simultaneous representatives and the pinned mates comparisons remain the
   substantial open work; no claim that it is already proved is made.
   Zero K or K' allows a zero row and a zero comparison. An empty open forces
   the other to cover X and gives the split sequence; if U = V, both equal X
   and the diagonal/difference sequence is split. These tests impose no extra
   hypotheses. Repeated LeanFinder/Loogle searches with cone/representative
   terminology, and local rg in both Lean roots, found only algebraic cone
   operations and single-cover presentations, not the relative theorem.
4. Read the existing one-cover presentation and functorial MV declarations
   before considering a shorter route. Verdict: neither identifies both rows
   and the prescribed global/overlap components. The final algebraic passage
   uses Mathlib directly. Every former direct proof dependency is now listed
   under No longer needed, with its continued use in the presentation plan
   explained. No global module pruning is claimed. Read
   dag/units/sk-thm-picard-semicon.json: its realized statement and step lists
   are empty; this delivery changes neither that record nor the unit's route.
5. Compared both nodes' Lean statement records, proof steps and dependencies
   with the source. Verdict: the completed boundary node records the actual
   SES transport proof; the new node records the remaining geometric plan,
   source, searches, provenance, chapter, unit and declaration. Its dependency
   set equals the union of its proof steps. No existing node statement changed.

Second-reading repairs: added private proof-plan imports to the open
presentation module, so the retained geometric dependencies really remain in
its import closure; completed the former-dependency inventory in the report;
recorded the independent duplicate search. Left the correct boundary proof
and both theorem signatures unchanged. One original hole is closed and one
new hole is added: decomposition, net zero, with no globally pruned module.
