## What changed

Proved `AlgebraicGeometry.IsCurve.assertions_of_constructible_approximation` with its exact
original signature and docstring. Its proof now constructs all eight fields. Private proved
helpers handle filtered cohomology continuity, vanishing, bijectivity, surjectivity, and
inheritance of primary/invertible torsion by monomorphisms.

Added the proved module `Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation` with
`AlgebraicGeometry.Scheme.exists_filtered_colimit_constructible_subobjects`. It uses the
existing constructible presentation, constructs its image diagram, proves image stages
constructible through kernels and cokernels, and proves the cocone universal property.
This is a presentation theorem on any Noetherian scheme; it contains no curve assertions.
Updated the parent DAG proof and added its presentation node. The sk-thm-p1 unit route
and its realized statements/steps stay in force.

Both modules compile locally without errors or warnings. All new helpers and the new public
theorem have complete proofs. Only proof imports were added to the existing module.

## Proved and sorry left

Proved the item's single original sorry:
`AlgebraicGeometry.IsCurve.assertions_of_constructible_approximation`
(node `lem-weil-pbc-constructible-approximation-assertions`). Also proved
`AlgebraicGeometry.Scheme.exists_filtered_colimit_constructible_subobjects`
(node `lem-pbc-u2-constructible-subobject-presentation`).

No sorry remains in either delivered module; none is split off. Existing imported theory
can still depend on sorry, as permitted by stage 3. In particular this does not claim that
constructible generation, directed derived continuity, or all of their dependencies are
axiom-free transitively. The delivery's axiom probe checks that no forbidden axiom is added.

C1-C3 use class representatives and zero images. C4-C5 apply H to F under their own
constructibility instances. C6-C7 use the canonical natural colimit comparison, with
invertible-order inheritance for C6. C8 represents and lifts a class at a stage. The primary
and invertible-order inheritance proofs use actual stalk injectivity, not torsion conditions
on arbitrary maps. Empty schemes and zero coefficients need no nonempty section assumption;
filtered indices are nonempty, the image universal property works for zero images, and all
cohomology arguments include degree zero wherever the assertion requires it.

## No longer needed

The original file had no proof imports to remove. During development removed the unused
`Sheaf.AlgebraicGeometry.EtaleInverseImageColimits` import and the redundant
`Mathlib.RingTheory.Noetherian.Basic` import from the new module.

The delivered proof does not need these original planned nodes/modules:

- `lem-kun-03sa` / `Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType`: use the
  existing qcqs `exists_filtered_colimit_constructible` directly in the image presentation.
- `lemma-weil-pbc-curve-filtered-cohomology` /
  `WeilConjectures.AlgebraicGeometry.Curve.Reductions`: this module imports the item, so using
  it here would cycle. Its index is also Type u, whereas generation supplies Type (u+1).
  Use the existing directed continuity and natural Ext comparison, after final reindexing.
- `lem-weil-pbc-inverse-image-preserves-colimits` /
  `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`: the inverse-image left-adjoint
  instances already give the required `isColimitOfPreserves` calls.
- The full independence/composition theorem
  `lem-weil-pbc-cohomology-pullback-functorial` /
  `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`: only the closed source lemma
  `Etale.cohomologyMap_map`, already exposed by the original statement import, is needed.

The Noetherian module-subobject and constructible-Serre nodes remain needed through the new
presentation theorem. The primary torsion definition remains used directly. Neither the
recent `Curve.ModuleSheafUnderlyingColimit` nor `Curve.EtaleSheafHLargeFilteredColimit`
module is needed: existing constant-coefficient preservation and directed continuity suffice.
These are pruning statements about this item's route, not claims that other targets stop
using these modules.

## Where the brief, the DAG or earlier work was wrong

The DAG's curve-filtered-cohomology declaration lives in the downstream Reductions module,
so it cannot be imported by this item. The arbitrary presentation's indexing universe is
u+1; its smaller-index theorem would not apply either. The proof now uses the existing
larger directed theorem plus `IsFiltered.exists_directed` and the Ext-derived comparison.
The two recent U2 colimit bridge modules were visible in repository source but absent in
the compiled cache; neither was copied or restated. Existing usable declarations suffice.

No mathematical statement correction was needed. The original natural-language argument is
realized, including image replacement to preserve torsion conditions and the conditional
finiteness fields. Sources were checked at [03SC](https://stacks.math.columbia.edu/tag/03SC),
[03SA](https://stacks.math.columbia.edu/tag/03SA), and
[09BH](https://stacks.math.columbia.edu/tag/09BH), since the local Stacks TeX is absent here.

The new presentation uses generic constructible-generation/comparison tools. These support
the same constructible reduction step and do not replace a unit's mathematical argument.
The maintainer may record any required cross-unit tool use; this worker changed no tool_uses.

## New nodes

`lem-pbc-u2-constructible-subobject-presentation`, in
`dag/nodes/sec-proper-base-change/lem-pbc-u2-constructible-subobject-presentation.json`,
states and proves a filtered constructible-subobject colimit presentation for a module sheaf
on a Noetherian scheme over a finite commutative ring. Its module is
`lean/Sheaf/AlgebraicGeometry/ConstructibleSubobjectPresentation.lean`. It is strictly the
presentation part of the argument, with no cohomology conclusion. LeanSearch was unavailable;
LeanFinder, Loogle and grep searches ran and found the image-map tools but no exact statement.
Blueprint searches for constructible subobject and filtered union found no duplicate.
Change record: `coord/changes/constructible-approximation-proof-scopes.md`. The initial dry run
compiled both modules and passed the axiom probe, then classified the additional namespace
openings as an interface change. The record documents these proof-scoping commands and the
unchanged public theorem signature; no importer adaptation is needed.

## Second reading by U2

1. Compared the delivered item module with the repository version. The theorem signature and
   its docstring are unchanged; only proof imports, namespace openings, private helpers, and
   the proof body changed. The added presentation module and node are declared in this report.

2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors or
   warnings. No `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` occurs in
   either delivered module. The declaration axiom probe reports no forbidden axioms.

3. Checked every added helper and the public presentation theorem against the existing library
   and Mathlib search results. The helpers are private reductions for filtered cohomology and
   stalk inheritance; the presentation theorem is a strictly smaller constructible-image
   statement and has its own node, source, and complete proof docstring. No target is restated
   or weakened, and zero sheaves, zero images, and empty schemes are covered.

4. Read the proof from the target downward. It uses the image presentation, scalar-forgetful
   colimit preservation, directed cohomology continuity, and cohomology-map naturality. The
   removed planned imports and nodes are listed under `## No longer needed`; no shorter route
   was found. The unit `sk-thm-p1` route and realized statements remain intact.

5. Compared both DAG nodes with the Lean declarations. The parent node records the helper route
   and pruned dependencies; the new node records its exact statement, source, proof steps,
   searches, Lean module, and unit. Proof origin and imports agree with the delivered code.

Changed after this reading: added this second-reading audit section required by the delivery
contract; no Lean declarations or DAG statements needed repair.
