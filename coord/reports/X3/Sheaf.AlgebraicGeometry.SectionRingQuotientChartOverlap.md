## What changed

The existing declaration `AlgebraicGeometry.Scheme.Modules.sectionRing_quotient_charts_overlap`
keeps its signature byte for byte. Its proof now obtains the underlying continuous-map
comparison, applies Mathlib `Scheme.Hom.ext`, and supplies the transported equality of
sheaf components. The three original public imports remain; the new comparison imports
are plain proof-only imports.

The first worker's `SectionRingQuotientChartOverlapCore.lean` was replaced by two new
modules, one per new statement: `SectionRingQuotientChartOverlapBase.lean` and
`SectionRingQuotientChartOverlapSheaf.lean`. The base-map statement remains the first
worker's statement. The sheaf-map helper now concludes equality of the pullback ring
homomorphisms on every target open, with the explicit `eqToHom` transport along the
supplied base equality. It no longer concludes the entire scheme-morphism equality.
Their docstrings contain complete natural-language proofs and the Stacks source places.
The original node's proof route and the two new nodes now describe precisely this
component decomposition. No existing statement, definition or visibility was changed;
there are no change records or forced adaptations.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.sectionRing_quotient_charts_overlap`
(node `lem-sc-section-ring-quotient-chart-overlap`), the sole original hole in the item.
There is no `sorry` in the item module.

Holes added and still open:

- `AlgebraicGeometry.Scheme.Modules.sectionRing_overlap_base_map`, in
  `Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapBase`, node
  `lem-sc-section-ring-quotient-chart-overlap-base-map`.
- `AlgebraicGeometry.Scheme.Modules.sectionRing_overlap_sheaf_map`, in
  `Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf`, node
  `lem-sc-section-ring-quotient-chart-overlap-sheaf-map`.

This is a decomposition: one upper hole closed and two strictly component-level holes
added, a local hole balance of -1. It is not a completed proof free of `sorryAx`, nor
claimed as positive net ledger progress. The global targets-closure ledger remains the
maintainer's measurement. No definition or arbitrary witness was introduced.

All three modules compile cleanly through `lcompile.py --all`. Scratch copies with
`#print axioms` for all three declarations reported exactly `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx`. The latter is expected from the two declared open components.
The scratch copies were removed. No forbidden declaration or implementation escape occurs.

## No longer needed

The item's unused plain import `Sheaf.Paper.NonvanishingSectionTrivializes` was removed.
It is not needed to elaborate the three delivered signatures or their current proofs.
The minimal public imports of the new modules are the section-ring definition, the
nonvanishing-locus definition, and Proj chart definitions.

Every old direct `proof_deps` entry was replaced in the item's node:
`def-pc-proj`, `def-sc-invertible-section-ring`,
`lem-weil-pbc-morphism-into-affine-scheme`, and
`lem-weil-pbc-nonvanishing-section-trivializes`.
They are still part of the documented mathematical proofs of the open components,
respectively the chart/nonvanishing arguments and affine comparison. They are recorded
there, rather than claimed to be used directly by the upper Lean proof. No mathematical
node was discarded and no whole-library module is claimed pruned. The discarded Core
file was only a first-worker sandbox addition, never a library module.

## Where the brief, the DAG or earlier work was wrong

The first report called the upper result proved without identifying the increased hole
count. Its sheaf-map theorem repeated the upper conclusion, adding only the base-equality
hypothesis, and the upper proof merely applied it. The repair states the actual sheaf
component and combines it with the base component using Mathlib extensionality.

The first worker's original node update was missing. The sheaf helper node incorrectly
copied the base helper's proof text. Both new node statements were not self-contained,
and the new nodes carried inherited J1 reviewer/landing records for work that had never
been reviewed or landed. These were removed. The local Stacks source mirror is absent;
the source was read at the official pages linked below.

Existing global preimage-forward/reverse lemmas were read. They give useful residue-field
proof templates, but their morphisms have domain X and their equations live on X; this
item has morphisms from U and V and equations on ambient images in another scheme.
Applying them would require substantial pullback/tensor/graded-section transport, not
a direct invocation. No comparison component was closed by those lemmas in this reading.

## New nodes

`lem-sc-section-ring-quotient-chart-overlap-base-map` states only continuous-map equality.
Its proof uses positive homogeneous chart membership, the residue-field nonvanishing test,
unit reflection along local stalk maps, and the T0 basis criterion. It contains no
sheaf-component conclusion.

`lem-sc-section-ring-quotient-chart-overlap-sheaf-map` states only equality of transported
pullback components after the continuous maps are identified. Its proof cancels free
generators on the common inverse images of affine homogeneous charts, compares all
fraction representatives, and uses sheaf locality. It contains no new base-map comparison
and no conclusion asserting equality of whole scheme morphisms.

Both nodes have complete source, statement dependencies, proof steps and their union as
`proof_deps`, search records, creation and blueprint ancestry, chapter/unit and verbatim
Lean signatures. Each new theorem has its own module. No change record is needed because
these are new statements and no existing interface changes.

## Second reading by X3

1. **Unchanged visible declarations: pass.** Diffed the item against the repository and
   compared its entire theorem signature as raw text through the result type: byte for
   byte identical. All original public imports and visibility remain. Only its proof and
   plain proof imports change. The two comparison statements are new sandbox declarations;
   their repairs do not alter any library declaration. No definition or target changed.

2. **Proof and axioms: pass for a decomposition.** Compiled all three delivered modules
   in import order. Independently compiled scratch copies printing each declaration's
   axioms: only the three permitted axioms and `sorryAx`. Exactly the two reported public
   named component theorems have `:= by sorry`; no partial proof, definition, axiom,
   unsafe/opaque declaration or implementation escape was introduced. The upper proof
   explicitly discharges the two premises of `Scheme.Hom.ext`; it is not one application
   of a renamed copy of the target.

3. **Open components: true, strict and needed.** Read the uniqueness parts of
   [Stacks 01N8](https://stacks.math.columbia.edu/tag/01N8) and
   [Stacks 01NK](https://stacks.math.columbia.edu/tag/01NK). The base component matches
   equality of underlying topological maps; the sheaf component matches cancellation of
   homogeneous fraction pullbacks after identifying inverse images. Hypotheses on X, L,
   positive degrees, nonvanishing loci, g/h and their fraction equations are retained
   literally. Both components now have complete proofs in their docstrings and nodes.
   Searched with different queries: LeanFinder for equality on a T0 basis and for scalar
   fraction cancellation, Loogle for `Scheme.Hom.ext`, the prescribed grep search for
   `isBasis_basicOpen`, and direct rg in Sheaf and the source ample/Proj modules.
   Mathlib supplies the final ext lemma, basis/T0 infrastructure and affine chart
   infrastructure; no duplicate ambient-image comparison was found. Checked the existing
   preimage-forward/reverse lemmas and explained the domain mismatch above. Edge checks:
   an empty overlap has no points and unique sections; a zero or nilpotent s/t has empty
   nonvanishing locus; over Spec of a field with trivial L, cancellation is division by
   a nonzero scalar; on a nonreduced scheme cancellation uses a module basis rather than
   reducedness; n=0 uses the tensor unit; d/e remain positive with no extra restriction.

4. **Shortest route and pruning: repaired.** Used Mathlib `Scheme.Hom.ext` directly for
   the component combination. Removed the unused proof import and the two-theorem Core
   packaging, retaining the original minimal signature imports. Every old direct
   proof dependency is accounted for in `No longer needed`. The existing
   `dag/units/sk-thm-curveestimate.json` has realized statement
   `thm-sc-proper-cohomology` and no realized steps; this item and its old proof dependencies
   are below that unit interface. Its realized route and chapter route remain unchanged.
   The source-based comparison route remains the same; no unit is bypassed.

5. **DAG agreement: repaired.** The item now depends on the two comparison nodes and
   records the final extensionality step as elementary. The base node records only the
   topological argument and no unnecessary affine-map dependency. The sheaf node records
   generator cancellation, affine comparison and sheaf locality, not the copied base
   proof. Both have `proof_deps` exactly the union of their step uses, source-based
   `proof_origin`, self-contained statements and verbatim Lean signature/module records.
   Removed false inherited reviewer records and supplied correct blueprint ancestry.

Changes by this reading: narrowed the sheaf helper to the actual component equality;
used `Scheme.Hom.ext`; replaced Core by one module per statement; completed proof
and source docstrings; repaired all three nodes and their signatures/searches;
removed the unused proof import; corrected the report's decomposition accounting.
