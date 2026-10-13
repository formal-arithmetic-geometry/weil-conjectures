## What changed

Completed `picardRightCechCup_cycle_comparison` without changing its signature.
Proved factor affine intersections, product intersection affineness, product cover
exhaustiveness and external coefficient quasi-coherence in Lean. Chose canonical
scalar Cech comparisons in all degrees, composed them with the fixed scalar-model
comparisons, and used extension-homology naturality to reduce to natural degrees.

Added `PicardScalarCechComparison`: its canonical comparison predicate is defined
by the existing module comparison through the two explicit additive Cech homology
identifications. Its existence theorem is proved from
`cechComparisonMapNaturality` and `moduleCechComparison_isIso_of_affine`.
The proof compares scalar multiplication transformations sectionwise and uses
`cechComplexFunctorHomologyIso_hom_smul` to prove k-linearity.

Added `PicardScalarCechExternalCup` for the remaining natural-degree compatibility.
It accepts arbitrary canonical linear comparison maps, not equivalences, and has
no affine, finite-cover, scalar-resolution or integer-extension assumptions.
The original cochain-coordinate hypothesis supplies its input directly.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.picardRightCechCup_cycle_comparison`.
Proved the new theorem:
`AlgebraicGeometry.Scheme.Modules.picardScalarCechComparison_exists`
(node `lem-sc-picard-scalar-cech-comparison`).

One new hole remains:
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`
(node `lem-sc-picard-scalar-cech-external-cup`).
This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes. It isolates the natural-degree compatibility of arbitrary supplied
canonical comparisons; all existence, affine geometry, scalar-model choice and
extension transport are proved in the delivery. There are no sorries in definitions
or private helpers and none left in the original module.

## No longer needed

No original public import was removed. The original theorem needs no direct import
of `Sheaf.AlgebraicGeometry.AffineModuleCechComparisonNatural` or dependency
`lem-sc-cech-comparison-natural`: no coefficient naturality of affine equivalences
is used to choose the individual canonical comparisons. The two existing comparison
nodes `lem-sc-cech-comparison-map-naturality` and
`lem-sc-cech-comparison-map-iso-affine` remain used by the new scalar comparison
proof, and `lem-sc-picard-cech-cup-pullback-compat` remains in the plan of the
remaining cup lemma. Their movement below the scalar helpers is not pruning.

The source library's proved `isAffineOpen_preimage_inf_preimage_pullback` replaces
a manual use of `pullbackSpecIso`; the affine fibre-product mathematical dependency
is retained. No tensor Kunneth theorem or tensor-total comparison is needed.
No global unreachability of these shared modules is claimed.

For completeness, the old direct proof dependencies absent from the new direct
list are `def-sc-field-linear-module-cohomology-operations`,
`lem-sc-cech-comparison-map-iso-affine`,
`lem-sc-cech-comparison-map-naturality`, `lem-sc-cech-comparison-natural`, and
`lem-sc-picard-cech-cup-pullback-compat`. All except
`lem-sc-cech-comparison-natural` remain below the new helpers, and the definitions
also remain in the original public signature closure. This removes only the
unused direct dependency on affine coefficient naturality, not a globally
unreachable module.


## Where the brief, the DAG or earlier work was wrong

The prior attempt left the original hole untouched despite useful helper statements.
Those helpers now form a compiling reduction; the scalar comparison existence step
is proved rather than left sorry. The existing general module cup/pullback theorem
speaks about global-section-module bilinear pairings and specified refinement maps,
whereas this item uses a k-linear external cochain component and scalar Ext cup.
The remaining helper records that interface bridge explicitly, with sources and a
complete proof plan. Existing signatures and definitions were not changed.

Small cases checked: an empty cover of an empty scheme gives zero Cech homology;
zero coefficients give zero classes; degree zero is the external section tensor
pairing. The compatibility lemma makes no unjustified invertibility assumption on
its canonical comparison maps. No blueprint unit statement or proof step is bypassed.

## New nodes

`lem-sc-picard-scalar-cech-comparison` matches the new canonical scalar comparison
predicate and its proved affine-cover existence theorem. Its proof constructs the
comparison from the existing canonical module map and proves scalar linearity.

`lem-sc-picard-scalar-cech-external-cup` is the sole new sorry, in its own module.
Its proof plan refines the projection covers, identifies front/back coordinates,
applies the canonical pullback and cup squares, then identifies their classes with
the scalar Ext definition using the characterized pullback and tensor coefficients.
Both nodes retain the item's chapter, unit and blueprint ancestor. Searches of
Mathlib and the whole imported blueprint found no exact statement; LeanSearch was
unavailable and is recorded as unavailable, not as an absence result.

## Second reading by S3

1. Compared the delivered original module with the repository using `diff` and
   the declaration parser. Its existing theorem signature and docstring are
   byte-for-byte unchanged; no existing definition or visibility changes.
   The two other modules are new and introduce only a characterized comparison
   predicate and the two reported theorems. Verdict: pass.
2. Compiled all three modules in import order through lcompile.py (exit 0).
   Inspected every proof and definition: one named public sorry, exactly
   `picardScalarCech_externalCup`, and no forbidden declarations or hollow data.
   Equivalences are chosen inside the theorem proof from canonical comparisons;
   no definition chooses an arbitrary witness from an unproved existence result.
   Explicit #print axioms checks show comparison existence uses only propext,
   Classical.choice and Quot.sound; the original and remaining compatibility
   theorems additionally use sorryAx, as reported.
   Verdict: a compiling decomposition, not a fully closed target proof.
3. Read the canonical module comparison characterization, additive Cech
   identifications, external component coordinates, scalar Ext cup and pullback
   definitions, and CechCupPullbackCompat. The remaining lemma removes affine
   geometry, comparison existence, scalar model choices and integer extension;
   it is strictly a compatibility step, not a renamed original theorem.
   The canonical predicate determines the comparison using invertible alpha
   for a cover, so arbitrary rescaled maps cannot satisfy it. Empty covers
   force empty schemes; their homology is zero. Zero coefficients give zero
   pairings; degree zero is the adjunction-unit tensor-section formula. Checked
   the source at https://stacks.math.columbia.edu/tag/0BED and
   https://stacks.math.columbia.edu/tag/0FKV. Repeated searches with
   `Canonical Cech comparison preserves tensor products on cocycles`,
   `HomologicalComplex.homologyMap`, and `comparison.*cup|cup.*comparison`,
   and local searches of scalar/Cech and cup/comparison names: no direct theorem
   for the scalar Ext interface. The left-cover comparison has different cover
   and transformation hypotheses; the right generator theorem imports this item.
   The bridge cannot be closed in a few minutes with those declarations.
   Verdict: true, sourced, needed and strictly simpler.
4. The proof takes canonical module comparison existence and affine isomorphism
   first, proves linearity with the upstream homology scalar-action lemma, and
   uses upstream affine pullback geometry and extension naturality directly.
   No tensor Kunneth theorem is used. All added imports of the original module
   are proof-only. The cube unit's `realized` record is unchanged (currently
   empty); its general-cube route is untouched. The remaining compatibility
   module retains the existing cup/pullback step as a proof import.
   Verdict: unit route preserved, no global module pruning claimed.
5. Checked both new nodes' Lean statements, source, chapter/unit, ancestor,
   creation records and search records; their proof dependency lists equal the
   unions of their step uses. The original node describes the geometry,
   comparison construction and transport actually written in Lean.
   Verdict: pass.

Second reading changed the remaining lemma's proof-only import to retain
`Sheaf.Paper.CechCupPullbackCompat`, and expanded its natural-language scalar Ext
identification rather than leaving that bridge implicit. No signatures changed.
The proof bodies were otherwise retained.
