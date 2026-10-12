## What changed

The item combines two strictly smaller conclusions, the affine-open section comparison and
sheafification comparison, in two new component modules. Its existing theorem signature is
byte-for-byte unchanged. Both components remain open, and their imports and docstrings now
retain the actual proof route. The two component imports in the item are proof-only.
No definition, existing public import, target statement or unit record changes.

## Proved and sorry left

Closed local hole:
`AlgebraicGeometry.qcoh_acyclic_derived_sections_comparison`
(node `lem-sc-qcoh-acyclic-derived-sections-comparison`), by combining the component witnesses.

Added holes:
- `AlgebraicGeometry.qcoh_acyclic_derived_sections_comparison_sections`
  (node `new-qcoh-acyclic-sections-component`).
- `AlgebraicGeometry.qcoh_acyclic_derived_sections_comparison_sheafification`
  (node `new-qcoh-acyclic-sheafification-component`).

This is a decomposition, not an axiom-free proof of the original theorem: one hole closed,
two added, local net minus one. Each added statement proves only one of the two independent
conclusions. No data is defined or chosen from an unproved existence theorem. All three
modules compiled locally. Scratch `#print axioms` checks showed only `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`.

## No longer needed

Removed direct proof imports of the item:
- `Sheaf.AlgebraicGeometry.DerivedCategory`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `Sheaf.Topology.RestrictInjectiveResolution`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`

The seven restriction/Leray/truncation/affine/projective imports are carried by the sections
component instead; DerivedCategory and SchemeDerivedDirectImage are already transitively
publicly available through DerivedSectionPresheaf. There are no modules pruned from the
item's transitive import closure. Removed the sections component's explicit public
Sheafification import: its signature does not need that import.

Every old direct proof dependency of the item has been replaced at that node by the two
component nodes. The former dependencies are:
`lem-pc-finite-support-hi`, `lem-pc-affine-vanishing`,
`lem-pc-leray-degenerate-sections`, `def-pc-derived-direct-image`,
`lem-pc-unbounded-derived-functor-cohomological-bound`, `def-pc-derived-category`,
`thm-sp-truncation-e2`, `def-weil-pbc-sheafification`,
`lem-sc-ringed-space-restrict-injective-resolution`,
`lem-pc-restrict-derived-direct-image-open`.
All are retained in the component plans, so none is claimed as a pruned DAG node.

## Where the brief, the DAG or earlier work was wrong

The first report omitted the decomposition count, named removed imports only by topic,
and implied pruning despite transferring the mathematical obligations to new holes.
The new nodes had placeholder statements rather than self-contained assertions, incomplete
proof plans, and searches that were absent from the actual search log. These are repaired.

The imported finite-support node's primary Lean record is the uniform vanishing theorem;
the quasi-coherence clause needed here is separately named in the same source library as
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`.
The component plan uses the quasi-coherence clause, not the uniform bound.
The old unit `sk-thm-picard-duality` has empty `realized.statement` and `realized.steps`;
this delivery does not fill or alter them. The ancestor finite-duality comparison remains
realized by this item, now through its two original conclusion components.

## New nodes

`new-qcoh-acyclic-sections-component` states the full natural, module-linear comparison
on the affine-open category, with all hypotheses. Its plan preserves original steps 1--3:
affine-open acyclicity, removal of the negative tail, and bounded-below hypercohomology
collapse. Its dedicated module has a complete natural-language proof and the required node
marker. LeanSearch returned Internal Server Error (logged as unavailable); actual LeanFinder,
Loogle and Mathlib grep searches found only generic sheaf
cohomology and exact-functor interfaces. No matching scheme comparison was found.

`new-qcoh-acyclic-sheafification-component` states the natural module-sheaf comparison
for the full presheaf, retaining the hypotheses of the item. Its source is Cohomology,
Tag 0D5X with Tag 0BKJ. Its dedicated module explains the K-injective computation,
sectionwise quotient, exact sheafification and descent of naturality. Generic exact-functor
and homology interfaces do not directly identify these two unbounded derived functors.
`RingedSpace.sheafification_cohomology` is an existential additive-group-valued comparison;
`higherDirectImageSheafifiedPresheaf` concerns etale abelian sheaves in nonnegative degrees.
Neither duplicates this module-valued comparison. No change records are needed.

## Second reading by F3

1. Compared the item with the repository using diff and checked the exact signature bytes.
   Verdict: unchanged. The only existing declaration changes its proof, and existing
   public imports are untouched. The other two modules and nodes are new.
2. Compiled all modules in import order using lcompile.py. Checked each declaration with
   `#print axioms` in scratch copies: only the three standard axioms and `sorryAx`.
   Verdict: valid reduction, with exactly two documented named theorem holes. No axiom,
   unsafe, opaque, implemented_by, extern, hollow definition or hidden proof hole.
3. Checked the components against both conjuncts and the definitions of derived section
   presheaf and direct image. They have the same hypotheses and each only one conclusion.
   Checked zero objects, f = identity and empty affine opens; both comparisons reduce to
   the standard affine acyclicity or zero comparison. Negative degrees are covered by
   shifting, and the unbounded case by the cohomological bound. Read the source arguments
   for Stacks 08D4/08D5 and the sheafification lemma from the installed Stacks source.
   Repeated searches with different queries and rg over both library roots.
   Verdict: true strict components with independent arguments; no full-item restatement.
4. Read the proof from its conjunction assembly downward. Existing generic interfaces
   offer parts of the arguments but no immediate proof of either full natural comparison.
   Checked the unit record and retained the ancestor route and original four proof steps
   in the components. Verdict: decomposition only; no module or old dependency is pruned
   from the transitive route. All removed direct imports/dependencies are listed above.
5. Checked the Lean signatures against the new nodes, restored the original proof plans
   and their dependency union, and checked each proof_deps equals the union of step uses.
   Verdict: node metadata matches the actual reduction and its remaining obligations.

Changed on second reading: expanded both component docstrings and node statements;
restored the sections proof-dependency imports and original steps 1--3; corrected the
sheafification source; replaced unsupported recorded searches with actual logged searches;
recorded exact new Lean signatures; removed the unnecessary explicit public import from
sections; rewrote the report to state the hole count and avoid claiming transitive pruning.
The original conjunction proof and all existing signatures were left intact.

Dry-run repair: the preflight requires LeanSearch as a separate search kind from
Loogle/LeanFinder. Ran both LeanSearch queries; the service returned Internal Server Error.
Recorded that unavailability without a mathematical no-match verdict.
