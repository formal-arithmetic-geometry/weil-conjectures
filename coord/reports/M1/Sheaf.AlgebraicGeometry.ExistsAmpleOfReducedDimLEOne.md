## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_reduced_dim_le_one`
with a complete Lean reduction. Its signature and existing docstring are unchanged.
The proof enumerates the irreducible components, constructs their reduced induced
closed subschemes, proves integrality and the required inherited instances, and
chooses ample modules by the dimension-zero or integral dimension-one theorem.
It constructs the intersection set and combines two new intermediate theorems
point by point using the actual definition of absolute ampleness.

Added `Sheaf.AlgebraicGeometry.GluedComponentAffineSection` for original proof steps
3–4 and `Sheaf.AlgebraicGeometry.ComponentSupportedAffineSection` for steps 5–7.
Each has one public named theorem with a complete source-based proof in its
docstring. Updated the parent node's proof, proof_deps and proof_origin and added
matching nodes for these intermediate statements. No existing interface changed.

Added proof-only imports of the two new modules and of the proved source modules
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`. The former supplies the
reduced vanishing-ideal subscheme instance; the latter supplies inherited
Noetherianity for finite-type closed immersions.

The three-module sandbox compiles. Edge cases were checked in the mathematical
argument: empty X, dimension-zero X, a single component (empty intersection set),
disjoint components including zero-dimensional ones, and intersecting components.
The finite-cover gluing statement also permits an empty cover, where its cover
hypothesis forces X empty. The supported-section statement has no conclusion at
intersection points; for an empty family its point hypothesis is impossible.

## Proved and sorry left

Closed the original one hole by decomposition (one closed, two added; net -1), namely
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_reduced_dim_le_one`
(node `lem-sc-reduced-dim-le-one-ample`), from named intermediate statements.
There is no sorry in the item's module. This is a reduction, not a claim that
all its transitive dependencies are sorry-free.

Two new sorries remain:

- `AlgebraicGeometry.Scheme.Modules.exists_glued_component_affine_section`,
  node `lem-sc-glued-component-affine-section`, module
  `Sheaf.AlgebraicGeometry.GluedComponentAffineSection`.
- `AlgebraicGeometry.Scheme.Modules.exists_component_supported_affine_section`,
  node `lem-sc-component-supported-affine-section`, module
  `Sheaf.AlgebraicGeometry.ComponentSupportedAffineSection`.

The first constructs the bundle and a single affine section neighbourhood of T,
without asserting ambient ampleness. The second works with an arbitrary given
bundle whose restrictions are ample and supplies sections only at points on a
unique component. Neither restates the target. The component enumeration,
component ampleness choices, uniqueness transfer, and assembly into IsAmple are
proved in the item's module.

## No longer needed

Removed these six direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.AffineCapSectionOpen`
- `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`
- `Sheaf.AlgebraicGeometry.AmpleIdealSection`
- `Sheaf.AlgebraicGeometry.ConductorSections`
- `Sheaf.AlgebraicGeometry.GlueComponentLineBundles`
- `Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover`

Their corresponding nodes `lem-sc-affine-cap-section-open`,
`lem-sc-ample-finite-principal-affine`, `lem-sc-ample-ideal-section`,
`lem-sc-conductor-sections`, `lem-sc-glue-component-line-bundles` and
`lem-sc-closed-affine-union-affine` remain needed in the new intermediate nodes'
proof plans. Their dependencies have moved down one level, with proof-only imports in the two new
modules; no mathematical branch or module is claimed pruned globally. Retained the component-intersection,
integral-dimension-one and zero-dimensional imports, all used directly. No
existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-route error found. The seven-step argument is retained:
steps 1–2 and the final pointwise combination are formalized here; steps 3–4
and 5–7 are the two new independent tasks. The local library's original imports
did not include the proved source Noetherianity theorem used for the reduced
component construction, so it was added as a proof-only import.

The TeX literature path in the node is not present in this clone. The source was
read from the available local copy `/home/ubuntu/c1-stacks-review/varieties.tex`
(09NX at lines 8080–8134 and 09NW immediately above), and checked against the
Stacks tag pages. LeanSearch returned HTTP 500; this is recorded as unavailable,
with real LeanFinder and source-grep searches used instead. No matching absolute
ampleness or component-supported section theorem was found in Mathlib. The
upstream field-relative IsAmple is a different predicate and was not used.

## New nodes

`lem-sc-glued-component-affine-section` is in
`dag/nodes/sec-curve-estimates/lem-sc-glued-component-affine-section.json`.
It packages the finite-set section choice, powering, gluing and finite closed
cover affineness of the original steps 3–4. Its statement takes already ample
component modules, so it does not hide their construction or prove the target.

`lem-sc-component-supported-affine-section` is in
`dag/nodes/sec-curve-estimates/lem-sc-component-supported-affine-section.json`.
It packages the ideal-supported product and conductor extension of steps 5–7.
It assumes a specified bundle with ample restrictions and a unique-component
point, and concludes the positive-power affine section data at that point.

Both nodes inherit the chapter and unit, cite the original blueprint ancestor
with the parent in via, and record actual searches. Blueprint searches for
09NX, 09NE, 09NW, component sections and conductor sections found no matching
blueprint node. No change record is necessary: no existing statement,
definition or public import changed.


## Second reading by M1

1. Compared the item against the repository with diff: its theorem signature and
   docstring are byte for byte unchanged. The only changes are the proof and private
   proof imports. The two other Lean modules and their nodes are new; there are no
   changed definitions, existing interfaces, or change records. Verdict: pass.
2. Compiled all three modules in import order using lcompile.py. A scratch copy with
   #print axioms for all three delivered declarations reported only propext,
   Classical.choice, Quot.sound and sorryAx. The item has no sorry; the two named
   new theorems each have exactly one sorry. No forbidden declarations or hollow
   definitions occur. Verdict: valid reduction conditional on the reported holes.
3. Read the helper signatures against Stacks 09NX and 09NW and the existing finite
   section, gluing, affine-cover and conductor lemmas. Tested empty cover, one
   component, disjoint components, intersecting curves and dimension-zero components.
   Finite closed-point intersections are discrete; the supported statement only
   concerns unique-component points. Neither helper restates the target. Each has
   a source, a full docstring argument, and a matching node. Independent LeanFinder
   searches using closed-cover and off-component wording found only structure-sheaf
   results; Loogle did not recognize the project's IsAmple predicate. Source grep
   found the existing planned lemmas and field-relative upstream ampleness, but no
   replacement for these two statements. Neither hole is a quick tactic closure.
   Verdict: true, strictly partial tasks; decomposition, not a net proof gain.
4. Checked every old proof_deps entry against the new route and the No longer needed
   list. The six old direct imports move to the helpers and remain in the target's
   import closure. No globally pruned module is claimed. The unit
   sk-thm-curveestimate realizes thm-sc-proper-cohomology, with no realized steps;
   the 09NX route through component ampleness and conductor extension is retained.
   Verdict: pass after restoring the missing proof-dependency imports.
5. Checked parent proof steps and proof_deps against the explicit component
   construction and two helper applications. Checked both new nodes' statements,
   lean records, sources, searches, blueprint ancestry, chapter, unit, creation and
   split status. Their proof plans now have matching private Lean imports.
   Verdict: pass.

Changed: restored the six planned proof imports in the helper modules; removed
unused public Separated imports from both helpers and the gluing helper's unused
Noetherian import, using Properties and ClosedImmersion for its actual signature;
expanded the power-ampleness argument in its docstring and node; added independent
search records; made the report explicitly count one closed hole and two added holes
as a decomposition with net -1. The original Lean proof required no repair.
