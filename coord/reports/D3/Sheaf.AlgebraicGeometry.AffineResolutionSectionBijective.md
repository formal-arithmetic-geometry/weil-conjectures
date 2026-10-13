## What changed

`Sheaf.AlgebraicGeometry.AffineResolutionSectionBijective` now proves
`AlgebraicGeometry.Scheme.Modules.affine_resolutionSectionClass_bijective` from
one general acyclic-complex section comparison, with its signature unchanged.

Put K = f_*I. `module_pushforward_injective_acyclic` proves positive module
cohomology vanishing on V for every term. `ordinaryHigherImage_isQuasicoherent`
and the resolution homology isomorphism prove quasi-coherence of every homology
sheaf of K. Open restriction preserves this property. Affine vanishing and
`exists_moduleCohomology_source_comparison` give its positive module cohomology
vanishing on V. The new comparison lemma consequently makes theta(V) invertible.
Expanding `resolutionSectionClass` shows that every remaining factor is an
isomorphism: resolution comparison, exact forgetting, homology of R.sections,
and exact evaluation. The last higher-image resolution comparison remains an
isomorphism after evaluation. Their composition is bijective in AddCommGrpCat.

Added five proof-only imports: SectionCohomologyThetaAcyclic,
ModulePushforwardInjectiveAcyclic, OrdinaryHigherImageQuasiCoherent,
ModuleCohomologySourceComparison, and the source library's Cohomology.Affine.Cech.
The original public imports and all existing signatures and visibility remain
unchanged. No definitions or other existing modules were adapted.

Both delivered modules compile through lcompile.py. The original module has no
sorry left; the new theorem has its entire proof postponed as required.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.affine_resolutionSectionClass_bijective`
(node `lem-pc-affine-resolution-section-bijective`), one of one original holes.

Added and still sorry:
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyTheta_isIso_of_acyclic`
(node `lem-pc-section-cohomology-theta-acyclic`), in the new module
`Sheaf.AlgebraicGeometry.SectionCohomologyThetaAcyclic`.

This is a decomposition: one hole closed and one added, net zero, not a claim
that all its mathematical dependencies are proved. The new theorem is for an
arbitrary nonnegative complex on an arbitrary open with two explicit acyclicity
hypotheses. It contains no scheme morphism, quasi-coherence, affine hypothesis,
injective resolution, or restricted-resolution choices. The original module
proves both hypotheses from existing declarations and combines the comparison
with the other isomorphisms in a complete Lean proof. It is not the original
statement under another name or a repackaging of its hypotheses.

## No longer needed

No original import was removed. All five new proof imports are used.

The direct proof no longer needs:

- `lem-pc-leray-degenerate-sections` / Sheaf.AlgebraicGeometry.LerayDegenerateSections;
- `lem-pc-higher-direct-image-open-restriction` /
  Sheaf.AlgebraicGeometry.HigherDirectImageOpenRestriction;
- `lem-weil-pbc-higher-direct-image-presheaf` /
  Sheaf.Paper.HigherDirectImagePresheaf.

These are removed from this item's proof_deps and are not directly imported.
They may remain in transitive imports or be needed by other users; this report
makes no claim that they leave the entire targets' import closure.

The normalization step comparing the particular map to a separately constructed
Leray edge is unnecessary. Bijectivity only needs R.sections to be an isomorphism;
R.augmentation and R.components are not used. Their fields and definitions are
unchanged. Every other original proof dependency is still used, including the
ordinary higher-image quasi-coherence and affine vanishing nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG's route is mathematically reasonable, but its two steps introduce a
normalization comparison unnecessary for bijectivity. A direct comparison for
section-acyclic complexes isolates the unresolved homological argument and
avoids all open-restriction and edge normalization glue in this module.
The item's node now describes this Lean route. The unit's own statement and
realized steps are untouched: this item is below those realizations.

LeanFinder, Loogle and Mathlib source searches found no exact acyclic
section/homology comparison. LeanSearch returned an Internal Server Error and
is recorded as unavailable, not a negative match. Blueprint searches for
hypercohomology, section/homology and acyclic terms were inspected; the general
spectral sequences already exist, but none states this normalized section-map
consequence. The new node cites them rather than duplicating their statements.

For its proof plan, the new node uses thm-sp-if-e1,
lem-sp-cartan-eilenberg-total-resolution,
lem-weil-pbc-ce-resolution-all-lower-bounds, and thm-sp-truncation-e2 as general
homological tools from their units. They supply resolution existence and the two
spectral sequences; they do not replace any step realized at the current unit
level. No tool_uses field belonging to the maintainer was modified.

## New nodes

`lem-pc-section-cohomology-theta-acyclic`, in
`dag/nodes/sec-proper-base-change/lem-pc-section-cohomology-theta-acyclic.json`,
is stated in `lean/Sheaf/AlgebraicGeometry/SectionCohomologyThetaAcyclic.lean`.
Its source is Stacks 015J (both hypercohomology spectral sequences), with 01E4
for the canonical cocycle map. Term acyclicity collapses the first sequence;
homology acyclicity collapses the second; the finite nonnegative filtrations
identify the same abutment. The cocycle computation identifies their composite
with theta evaluated on V. Both vanishing premises are indispensable in this
general statement. The proof is given in the theorem docstring and the node.

Edge cases checked in the argument: degree zero uses kernels and augmentation;
an empty open has zero section groups; a zero complex has the unique comparison
between zero groups. No degree bound, nonempty-open assumption, or separatedness
stronger than the original quasi-separatedness was introduced. There are no
change records because no existing interface changed.

## Second reading by D3

1. **Interface and statements.** I compared the delivered affine module with the repository version. The existing theorem signature and all existing declarations are byte-for-byte unchanged. The split theorem has a new, explicit acyclicity statement and does not restate the target.

2. **Compilation and proof checks.** Both delivered Lean modules compile with `lcompile.py --all`. The affine target has no remaining `sorry`; the only remaining `sorry` is the named split theorem `sectionCohomologyTheta_isIso_of_acyclic`. No forbidden declarations or hollow definitions were added.

3. **Truth and strength of the split.** The split theorem is the standard Cartan–Eilenberg comparison under term and homology section-acyclicity. Its hypotheses are used separately to collapse the two spectral sequences, and its conclusion is exactly the evaluated theta isomorphism required by the target. The node supplies its source, proof plan, and declaration metadata.

4. **Pruning and imports.** I checked the proof imports and found all five added imports used. No original public import was removed, and the report correctly records the three old proof dependencies bypassed by the direct comparison. The proof keeps the unit route's realized nodes while avoiding unnecessary Leray normalization.

5. **DAG and unit consistency.** The target and split-node `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof and the unit `sk-thm-p1` remains unchanged. No statement or definition change record is needed.

I changed only this report section; no Lean code, declarations, or DAG metadata required repair.
