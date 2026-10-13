## What changed

The signature and docstring of
`AlgebraicGeometry.exists_affine_chart_sections_colimit_comparison` are unchanged.
Its proof now combines a geometric ring-colimit presentation with a proved, general
module-sections transport theorem. All three new modules have their own DAG nodes.
The original node records the implemented route.

`AffineChartRingColimitGeometric` proves the ring-colimit comparison from an affine
scheme limit on the upper tail. It forms the contravariant global-sections diagram,
uses Mathlib's preservation of colimits of affine schemes, constructs q by uniqueness
of colimits, and applies appTop to the geometric projection equation. Cancelling the
stage isomorphism gives exactly the required ring-map equation.

`ModuleSectionsPullbackIsoTransport` is fully proved for arbitrary scheme isomorphisms
and arbitrary module sheaves. Pullback composition gives the comparison over the ambient
scheme. The existing, proved `pullbackIsoPushforwardInv` identifies isomorphism pullback
with inverse pushforward. On top sections that is restriction along the inverse ring map.
Uniqueness of left adjoints identifies scalar extension with that inverse restriction.
Evaluation of the two module-sheaf comparisons completes the proof. No affine or
quasi-coherent hypothesis is needed for this component.

The remaining geometric construction is isolated in `AffineChartUpperTailLimit`:
a limiting diagram of affine stage charts, with stage and vertex isomorphisms and their
projection equations. It has no ring-colimit or module-sections assertion. All data
obtained from its existence statement is eliminated inside theorem proofs, never used
to define an object from an arbitrary unproved witness.

Validation: all four modules compile through lcompile.py --all. The delivery dry run printed OK: the set compiles and passes preflight except for
the second-reading section, which the tool correctly leaves to the second reader.
The axiom probes found no forbidden axioms. Nothing was pushed.

## Proved and sorry left

Closed original hole:
- `AlgebraicGeometry.exists_affine_chart_sections_colimit_comparison`
  (lem-pc-affine-chart-sections-colimit-comparison).

New declarations proved with complete Lean proofs:
- `AlgebraicGeometry.exists_affine_chart_ring_colimit_geometric`
  (new-affine-chart-ring-colimit-geometric).
- `AlgebraicGeometry.nonempty_module_sections_pullback_iso_transport`
  (new-module-sections-pullback-iso-transport).

Added and remaining hole:
- `AlgebraicGeometry.exists_affine_chart_upper_tail_limit`
  (new-affine-chart-upper-tail-limit), in
  Sheaf.AlgebraicGeometry.AffineChartUpperTailLimit.

One original hole closed and one lower hole added: decomposition, zero net hole gain.
The residual statement contains neither a module M nor any global-sections or colimit
object, so it is strictly the geometric part of the original argument. The general
sections-transport theorem is proved independently of any inverse-limit hypothesis.

Edge cases checked against the construction: the upper tail contains i even when the
preorder has equivalent indices; common upper bounds make it directed and connected.
Empty charts give empty affine schemes and zero rings, for which the same categorical
limit argument works. The sections proof uses equivalences of categories and works
for zero modules and identity isomorphisms, without finite presentation, nonzeroness,
flatness or quasi-coherence assumptions.

## No longer needed

No existing imports were removed from the original module, and no global pruning is
claimed. Its existing public imports are unchanged. New imports in the original module
are proof-only imports of AffineChartRingColimitGeometric and
ModuleSectionsPullbackIsoTransport. The ring helper imports the geometric limit helper
and Mathlib.AlgebraicGeometry.AffineScheme only for its proof. The general transport
helper needs only Mathlib module sheaves and scalar extension in its public interface;
it does not import BaseChangeConventions, TensorPullback, finite-presentation descent,
or any quasi-coherence theory for its proof.

The parent's previous direct proof dependencies def-pc-base-change,
def-pc-fibre-product and def-pc-module-pullback are replaced by the two new component
nodes. The first two remain part of the geometric limit helper's planned argument;
module pullback remains part of the transport statement. They are redistributed,
not globally pruned. No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original single proof step concealed both the geometric limit construction and the
arbitrary-module transport calculation. These are now separated, and the latter is
proved using existing library declarations. In particular, an arbitrary ring
isomorphism alone is insufficient for the sections comparison: the geometric
isomorphism and its equation over the ambient scheme are retained in the ring helper.

Tag 01I6 describes quasi-coherent affine sheaves; the transport of arbitrary modules
here uses the module-pullback adjunction and composition of Tags 0095 and 0097 instead.
The cited Stacks pages were read directly because the listed local TeX files are absent
on this machine. Tag 01ZR's first proof sketches the affine reduction; the remaining
geometric helper docstring expands the upper-tail and pullback-limit details rather
than claiming that the source gives this exact chart formula.

LeanFinder found general affine-limit and module-pullback tools, no exact comparison.
Loogle reported Scheme.Hom.appTop as an unknown identifier; local source inspection
confirmed the actual declaration and its composition theorem. Local rg located the
proved pullbackIsoPushforwardInv and Mathlib's preservesColimit_Γ. The searches are
recorded in the new nodes. LeanSearch returned Internal Server Error and is recorded
as unavailable without a verdict.

## New nodes

new-affine-chart-upper-tail-limit, module
Sheaf.AlgebraicGeometry.AffineChartUpperTailLimit: the geometric limit of affine stage
charts over the upper tail, with the compatible chart and ambient projection equations.
This is the only new hole; its docstring contains the full geometric proof plan.

new-affine-chart-ring-colimit-geometric, module
Sheaf.AlgebraicGeometry.AffineChartRingColimitGeometric: a proved conversion of that
geometric limit into the chart-ring colimit and the induced ring-map equation.

new-module-sections-pullback-iso-transport, module
Sheaf.AlgebraicGeometry.ModuleSectionsPullbackIsoTransport: a proved theorem transporting
sections of module restrictions across any scheme isomorphism commuting with their
maps to an ambient scheme. It assumes neither affineness nor quasi-coherence.

No change record is required: no existing statement, definition, visibility or public
import changes, and no other existing module is adapted.

## Second reading by U4

1. Compared every delivered module with the repository. Only
   AffineChartSectionsColimitComparison already exists. Its theorem signature and
   docstring are byte-identical; its public imports are unchanged. The diff adds
   two proof-only imports and replaces the proof. The other three modules are new.
   Verdict: no accidental interface or definition change; no change record needed.
2. Independently compiled all four modules with lcompile.py --all. All pass without
   errors or warnings. Scanned every delivered Lean file: the only sorry is the
   named exists_affine_chart_upper_tail_limit theorem; there are no definitions or
   forbidden declarations. A separate scratch module printed axioms of all four
   theorems. The transport theorem uses only propext, Classical.choice, Quot.sound;
   the other three additionally use sorryAx from the geometric hole. Verdict: the
   proved components are kernel-checked; the original item is a decomposition,
   not an unconditional completed proof. One original hole closed, one added,
   zero net hole gain. The scratch module was removed before delivery.
3. Read the remaining geometric statement, its full docstring proof and node.
   Cofinality of the upper tail uses common upper bounds, not antisymmetry. The
   nonempty connected tail permits forgetting the over-category limit; base
   change preserves it. Pullback pasting gives both geometric equations, and
   affineness follows by base change from affine schemes. The statement remains
   valid for empty charts, zero rings, identity diagrams and equivalent preorder
   indices. It neither restates the ring/module conclusion nor chooses data for
   a definition from an unproved existence theorem. Independently searched with
   LeanFinder for connected limits of fibre products, Loogle for pullback/limit
   types (identifier unavailable), and rg/msearch for connected-pullback limits
   and pullback-composition isomorphisms. Found supporting Mathlib tools, no exact
   geometric-chart theorem. Verdict: true, needed, strictly geometric residual.
4. Read from the parent downward through the ring helper and transport proof.
   The latter uses the proved upstream pullbackIsoPushforwardInv and Mathlib
   adjunction uniqueness, so no quasi-coherence hypothesis is hidden. The ring
   helper genuinely converts a scheme limit using preservesColimit_Γ and checks
   the projection equation by appTop. Independently inspected the existing proved
   AffineBaseChangeChart.isColimit_cocone and
   exists_affineOpen_directedRingSystem: they concern inverse-image opens and do
   not directly provide the chosen-cover scheme comparisons and ambient-map
   equation. Using them still requires that geometric comparison argument; no
   quick closure of the remaining hole was found. Imports support signatures,
   instances or these proof steps; added proof imports are plain imports. The
   three old proof dependencies are all accounted for under No longer needed.
   Checked dag/units/sk-thm-picard-semicon.json: this node is not a realized unit
   statement or step, and the delivery bypasses no realized unit node. Verdict:
   legitimate reduction; no global pruning claimed.
5. Checked parent and all three new nodes against the Lean declarations, including
   proof-dependency unions, sources, origin, creation, blueprint, chapter, unit and
   Lean records. Read Stacks 01ZR, 0095 and 0097 directly: 01ZR sketches the affine
   reduction, while 0095/0097 give module pullback and composition. The detailed
   geometric proof is explicitly attributed to the agent. Verdict: consistent
   after the metadata repairs below.

Second-reading changes: replaced the three new nodes' abbreviated Lean statement
records with the exact multiline signatures. Rewrote the ring helper's proof
record to describe its actual use of the geometric helper, the affine
sections-colimit preservation theorem, colimit uniqueness, and appTop cancellation.
Clarified the ring and module helpers' proof-origin records. Added this independent
review and search evidence. No Lean proof, statement, definition or import needed
repair.
