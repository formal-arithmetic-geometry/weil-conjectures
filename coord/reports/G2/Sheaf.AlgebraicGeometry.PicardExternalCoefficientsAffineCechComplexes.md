## What changed

Replaced the one hole in
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_cech_complexes`
by assembling normalized degreewise comparisons with
`HomologicalComplex.Hom.isoOfComponents` and taking the inverse. The theorem signature
and its public imports are unchanged. The second reading removed the redundant
private direct Terms import (available via Differential), and added a private
ExternalGlobalSectionsTensorAffine import to the Terms module for its revised
proof plan. Two new modules separate the affine section
comparison from the alternating differential calculation. The pure-tensor section
map and normalization predicate are real constructions using pullback units,
restriction sections, and `tmulSection`; no data is selected from an arbitrary
existence theorem.

## Proved and sorry left

The original hole in `picardExternalCupCoefficients_affine_cech_complexes` is closed
by a decomposition, not a sorry-free proof of the geometric assertion.

The one new hole is `AlgebraicGeometry.Scheme.Modules.picardAffineCech_normalized_terms`
(node `lem-sc-picard-external-coefficients-affine-cech-terms`), in
`Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechTerms`.
It states degreewise isomorphisms with a concrete pure-tensor normalization, without
any differential or cohomology conclusion. It is a strict part of the original
argument, rather than an isomorphism of complexes under another name.

`AlgebraicGeometry.Scheme.Modules.picardAffineCech_normalized_differential` has a
complete Lean proof, using tensor induction, native Cech differential coordinates,
integer-additivity of tensor sections, pullback-unit naturality, and composition
of restriction maps. Its three private helpers are proved without holes.
The item has zero remaining holes. Holes closed: 1; holes added: 1; local net: 0. The target-closure ledger determines project progress.
This delivery is a decomposition with a proved differential step.

## No longer needed

No original imports were removed. No original geometric dependency is pruned:
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-module-pullback-tensor`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
remain needed below the normalized term comparison, partly via the existing
external affine-section bijection. They are no longer direct proof dependencies
of the assembled complex isomorphism. The redundant private direct import
Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechTerms was removed
from the item; its module remains reached through Differential. The term node
now reuses lem-sc-external-global-sections-tensor-affine, so affine pullback
sections and quasi-coherent tensor sections are needed under that existing node
rather than named directly in the term node. No unit statement or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

Two existing proof dependencies have Mathlib matches instead of Lean records:
affine spectrum pullbacks and open-immersion restriction versus pullback.
This is supported by the standing brief and causes no obstruction.
The item is not itself a recorded realization of the unit statement or a unit step;
the unit record was read and its route remains unchanged.
LeanSearch returned HTTP 500 for both semantic queries. The unavailability is
recorded accurately; LeanFinder, Loogle, Mathlib source searches and library source
searches were run. No direct external-coefficient Cech comparison was found.

## New nodes

`lem-sc-picard-external-coefficients-affine-cech-terms` records normalized additive-group
isomorphisms in each degree. It has no differential or cohomology conclusion. Its
proof follows the original affine chart and finite-product steps. The normalization
formula is defined by actual pullback-unit and tensor-section constructions. Finite
empty index sets, empty intersections and V, and zero coefficients satisfy the
same section and tensor formulas.

`lem-sc-picard-external-coefficients-affine-cech-differential` records differential
compatibility for arbitrary normalized degreewise comparisons. It assumes no
quasi-coherence, affine hypothesis, finite index set or cover, and asserts no
existence of the comparisons. It is separate from the affine bijectivity argument.
The face set remains finite in every degree even for an infinite index set.
The theorem is proved in the delivery, so it introduces no further hole.

The module set is compiled in import order by `lcompile.py --all`. The final
delivery dry run checks compilation and axioms for every declaration. The
independent second reading below completes the review for delivery.

## Second reading by G2

1. PASS: diff against the repository shows the original declaration signature and
   visibility are byte for byte unchanged. Only its proof and private proof imports
   change. No target, existing definition, or existing hypothesis was modified.
2. PASS: all three modules compile individually in dependency order through
   lcompile.py. There is exactly one named theorem with sorry, the normalized term
   comparison reported above; no definition contains sorry or selects its data from
   that theorem. The adjunction selected by PureSection has its unit pinned on every
   section by exists_tensorPullbackAdjunction, whose proof is present. Hence this
   construction uses specified data, not an arbitrary existential witness. Explicit
   axiom checks cover the pure section, normalization, term theorem, differential
   theorem and original theorem; the delivery probe checks all file declarations.
3. PASS with repair: the new hole is only the affine degreewise bijectivity and
   normalization step, with no differential conclusion. Its finite-product argument
   includes an empty index type; empty affine factors and zero modules give zero
   sections. Repeated indices merely repeat intersections and face restrictions.
   Independent LeanFinder and Loogle searches and rg of the current library found
   TensorProduct.piRight and the proved
   externalGlobalSectionsTensor_bijective_of_isAffine. These supply proper parts of
   the new hole, not its chart transport or full statement. Repaired its docstring
   and node plan to reuse those results explicitly instead of rebuilding their
   algebra. The differential proof was read through tensor induction, coordinate_d,
   sectionUnit_restrict and the final two restriction identities; it proves precisely
   the displayed square without affine or finiteness assumptions.
4. PASS with repair: assembly by isoOfComponents and inverse is the correct direction.
   Removed the redundant private direct import of the Terms module from the item;
   Differential publicly imports it because its signature uses those definitions.
   The remaining original public imports supply the original signature. The unit
   sk-prop-av-cube realized fields contain no occurrence of this node, and no unit
   route or realization is changed. No original geometric module is pruned from the
   import closure: the shorter affine-section route reuses them below its existing
   affine-section theorem.
5. PASS with repair: the original node's proof and proof_deps name exactly the two
   new theorems used by the Lean proof. New nodes have source, full statement, proof,
   searches, creation, blueprint, chapter, unit and Lean records. Updated the term
   node's proof_deps to the chart-transport ingredients plus the existing affine
   external-section node, matching the repaired shortest proof plan. The differential
   node records its elementary restriction-and-additivity proof. Lean signatures in
   all three node records match their modules.

Second-reading changes: removed one redundant private import, added the private
affine-section import required by the revised proof plan; improved the remaining
hole's proof docstring and DAG plan to reuse the existing affine external-section
bijection and Mathlib finite-product tensor equivalence. No Lean proof or signature
needed repair. This remains one hole closed and one added, local net zero, a decomposition
with a proved differential step, not a completed geometric proof.
