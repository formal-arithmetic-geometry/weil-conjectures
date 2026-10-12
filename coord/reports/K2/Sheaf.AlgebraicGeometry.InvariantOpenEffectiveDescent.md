## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent` by a
compiling reduction. The existing declaration and its signature are unchanged. The proof
selects a point-indexed subcover and explicit local effective witnesses, invokes the new
geometric chart-construction theorem, proves global cartesianness by
`Scheme.isPullback_of_openCover`, and proves transport invariance by naturality,
restriction to inverse-image opens, and `Scheme.hom_ext_of_forall`.

Added `Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts`, containing only the remaining
geometric construction, and updated the parent DAG proof to match the Lean.
All new imports of the parent are proof-only imports.

## Proved and sorry left

Closed: `CategoryTheory.Over.DescentDatum.isEffective_of_effective_open_cover`
(node `lem-pd-effective-invariant-open-cover`). No sorry remains in the assigned module.

Added one sorry: `CategoryTheory.Over.DescentDatum.exists_glued_effective_model_charts`
(node `lem-pd-glued-effective-model-charts`). This is a decomposition, not a net hole
reduction: one upper hole closed and one lower geometric hole added. The remaining lemma
asserts only local chart squares and open embeddings for fixed effective models; it does
not assert global cartesianness or transport invariance. Those are proved by the parent.
No definitions are added and no data are defined by choosing an arbitrary unproved witness.

Edge cases checked: an empty index forces V empty, and empty local opens descend to empty
models because p is jointly surjective. Duplicate and overlapping opens are handled by
unique descended transitions. Arbitrary large index universes in the parent are reduced
to a point-indexed subcover, so the new theorem only requires the scheme universe.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` and
`Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent` from the assigned module.
Their nodes `lem-galois-fpqc-morphisms-descend` and
`lem-weil-pbc-open-subscheme-fpqc-descent`, and `lem-weil-pbc-glue-schemes`, remain needed
by the new chart-construction node. They are moved below that node, not globally pruned.
No whole node or module is claimed globally unnecessary. The remaining sorry-only module
imports only what its signature needs; its proof dependencies remain documented in its node.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing open-descent and morphism-descent interfaces do
not already assemble the geometric charts in transport form. That assembly and its local
chart-square checks are isolated as the remaining theorem. The original route is retained.
`coord/delivery-errors.md` currently has no section I; its available rules were checked.
LeanSearch returned Internal Server Error and is recorded as unavailable, not as no match.

## New nodes

`lem-pd-glued-effective-model-charts`, in
`dag/nodes/sec-picard-framework/lem-pd-glued-effective-model-charts.json`, states the
geometric chart construction from fixed local effective models (Stacks Tag 0AP4).
Its new module is `lean/Sheaf/AlgebraicGeometry/GluedEffectiveModelCharts.lean`.
The source construction and the local cartesian verification are expanded in its docstring
and DAG proof. No statement changes or change records are required.

## Second reading by K2

1. **Visible declarations: pass.** Diffed the parent against the repository and compared
   its theorem signature byte for byte: unchanged. Its docstring is also unchanged.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`. There are
   no changed definitions or statements requiring a change record.
2. **Lean proof and axioms: pass, with the reported remaining hole.** Both modules compile
   cleanly in import order through `lcompile.py`. Scratch `#print axioms` checks for both
   declarations report only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is the single named chart-construction hole, not a hidden proof hole.
   There are no definitions, forbidden declarations, or arbitrary witnesses used to
   define data. The parent chooses models from its given effectivity hypotheses within
   its proof and proves both required conclusions.
3. **Split-off statement: pass as a decomposition.** Matched hp, D, the open cover,
   transport compatibility, fixed models, cartesian squares, and invariance with the
   new node and Stacks Tag 0AP4 (https://stacks.math.columbia.edu/tag/0AP4). Each conclusion
   has a role: the open immersions and joint cover form the cover of W0, the equations
   over Y transport the local squares, and the chart squares identify their pullbacks.
   This is the geometric part of the argument; it does not assert global cartesianness
   or global transport invariance. Empty I forces V empty; an empty U_i forces W_i empty
   by fpqc surjectivity. Identity p and repeated opens reduce to ordinary open gluing.
   No affine, separatedness, finiteness, or nonemptiness assumptions are hidden.
   Its docstring gives the overlap descent, inverse/cocycle checks, structure-map gluing,
   and local chart-square proof. Repeated LeanFinder and Loogle searches using local
   representability and invariant open subobjects, and rg of both library roots, found
   no duplicate. Mathlib LocalRepresentability.representableBy needs an already-built
   sheaf and relatively representable open charts; it does not eliminate the missing
   descended-overlap construction here. This hole cannot be closed in a few minutes.
4. **Top-down route and pruning: pass.** The parent genuinely proves global cartesianness
   using Scheme.isPullback_of_openCover, and proves invariance on inverse-image opens
   using transport_homMk_comp, hcompat, hinv and Scheme.hom_ext_of_forall. This is not
   one application of a renamed version of the parent. All old proof dependencies are
   accounted for: descent-datum and morphism-gluing remain direct; open descent,
   fpqc morphism descent and scheme gluing move beneath the chart node. No whole module
   is globally pruned. The unit's realized record currently has empty statement/step
   lists; this delivery leaves it unchanged and retains the same effective-descent
   gluing route below that unit. Removed an unnecessary public Pullbacks import from
   the new module, and checked compilation without it. Kept the parent's proof-only
   imports for its explicitly used pullback-locality and morphism-locality lemmas.
5. **DAG agreement: pass.** The parent node's four steps follow the point-indexed cover,
   chart construction, local-to-global pullback proof and transport restriction proof.
   Its proof_deps is precisely the union of its step uses. The new node matches the
   Lean signature verbatim and has source, complete proof steps, their dependency
   union, proof_origin, searches, created/blueprint records, chapter/unit and Lean record.
   The geometric construction still open is honestly documented as such in the report.

Changed in this reading: removed the unused public
`Mathlib.AlgebraicGeometry.Pullbacks` import from `GluedEffectiveModelCharts.lean`;
added this review record. Statements, definitions, and the valid parent proof were retained.
One original hole is closed and one strictly geometric hole is added: net zero, decomposition.
