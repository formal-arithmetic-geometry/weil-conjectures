## What changed

The item theorem `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_local_cohomology`
has a complete Lean proof at its original signature. It constructs a finite affine open cover,
proves every nonempty finite intersection affine from the given affine diagonal, and constructs
the scalar Cech-to-global-cohomology comparison from the existing alpha/beta maps and injective
resolution comparison. Field freeness/flatness supplies exact tensorRight; its homology
comparison, the tensor of the scalar comparison, and the geometric affine-right comparison
compose to the stated additive-group isomorphism.

Two new modules expose strictly intermediate parts of the original plan:
`Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComplexes` states the termwise
product-cover complex isomorphism, and
`Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison` proves the passage
from that complex to open cohomology. The latter independently proves product-intersection
affineness, covering, and quasi-coherence, and uses the existing natural open restriction
comparison and affine beta augmentation. All proof-only imports are non-public. No existing
signature, visibility, definition, or target was changed; no forced adaptations are needed.

The geometric remaining statement is a complex isomorphism, has no degree q, needs no
covering assumption, and does not mention derived functors or global cohomology. The proof
combining it with the rest is substantive Lean in the item and the comparison module.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_local_cohomology`
(node `lem-sc-picard-external-coefficients-affine-local-cohomology`).

Added one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_cech_complexes`
(node `lem-sc-picard-external-coefficients-affine-cech-complexes`). Its proof is exactly
`by sorry`; its docstring and node give the complete affine section, restriction, finite
product, and differential argument. No data is selected from this holed existence theorem
outside a theorem proof.

Also proved the new public intermediate theorem
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_cech_comparison`
(node `lem-sc-picard-external-coefficients-affine-cech-comparison`) and all private helpers.
No `sorry` remains in the item or in the intermediate cohomology comparison module.

This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero new-hole progress. The item still depends on existing named library holes in
its affine cohomology and tensor ingredients; it is not claimed axiom-free.

Edge cases checked on the interfaces and arguments: an empty X admits an empty index set;
all Fin(n+1)-tuples then have no coordinates, with zero complexes. Empty V, empty
intersections, and zero coefficients have zero section complexes. No nonempty index-type,
finite dimensionality, acyclicity, quasi-compactness of Y, or affine diagonal of Y was added.
The pure termwise formula uses a single affine right factor and is not the generally false
claim that the two-cover Kunneth tensor total is isomorphic to the product-cover complex.

## No longer needed

No original import was removed, and no whole proof-dependency branch is claimed pruned.
The original three public statement imports are needed by the unchanged interface.
Redundant imports tried during development were removed:
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`,
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (their APIs are already public
through the remaining imports).

The original direct dependency `lem-sc-cech-comparison-map-iso-affine`
(`Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine`) is replaced by the more direct
beta/alpha argument using `lem-sc-module-cech-beta-affine-quasi-iso` and
`def-sc-module-cech-comparison`. Its wrapper is not imported or needed by this proof.
The original fibre-product, affine pullback sections, open-immersion restriction,
and tensor-section dependencies remain needed in the termwise geometric lemma, not
as direct dependencies of the upper theorem. `def-sc-open-module-cohomology` remains
a statement dependency. The finite affine cover, affine diagonal intersections,
and field tensor exactness remain actual dependencies. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated plan is mathematically consistent. The original item did not yet import the
modules of its proof dependencies despite the standing brief describing that arrangement.
The exact APIs needed were found in the library and imported as proof-only dependencies.
Using the native Cech complex followed by global scalar restriction avoids introducing
another definition of scalar Cech cohomology.

The local source path `literature/stacks-project/varieties.tex` is absent on this machine.
The source was read online at https://stacks.math.columbia.edu/tag/0BED: the affine-open
paragraph explicitly states the equality of complexes used here. New nodes record that
URL and place. The unit `sk-prop-av-cube` and its realization record were read; this work
only expands the existing lower external-coefficient calculation and changes no unit route.

Searches ran through msearch.py (queries and digests in searches.jsonl): LeanSearch was
unavailable (Internal Server Error), LeanFinder found only scheme-section and generic Cech
APIs, Loogle found mapHomologyIso, and the Mathlib regex search found zero external Cech or
cohomology comparisons. Repository and source rg searches found the higher Picard/Kunneth
modules and affine section ingredients, but no reusable comparison at this interface.
Blueprint searches for external Cech affine, Cech cohomology affine, and tensor Cech
found no duplicate blueprint node.

## New nodes

`lem-sc-picard-external-coefficients-affine-cech-complexes`:
`lean/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineCechComplexes.lean`.
This is the remaining termwise complex isomorphism; its finite family need not cover X,
and it makes no cohomology assertion. Its arguments and docstring include the balance
relations, pure-tensor restriction equations, finite product inverse, and differential
compatibility from the original plan.

`lem-sc-picard-external-coefficients-affine-cech-comparison`:
`lean/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineCechComparison.lean`.
This is proved from that complex isomorphism and existing library comparisons; the affine
geometry and quasi-coherence are proved explicitly. It identifies open cohomology with
homology of a termwise tensor Cech complex, before exact tensor and the first factor
Cech/global comparison are applied in the item.

There are no change records because no existing interface was changed.

## Second reading by P3

1. Compared the delivered local-cohomology module with the repository version. The target
   signature is byte-for-byte unchanged; the added imports are proof-only, and the two new
   modules and DAG nodes are included in the delivery. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with
   no errors. The only remaining `sorry` is the named split theorem
   `picardExternalCupCoefficients_affine_cech_complexes`, with its matching node and
   docstring. No forbidden declarations or hollow definitions were found. Verdict: pass.
3. Checked the new Cech-complex and Cech-comparison statements against their signatures,
   edge cases, docstrings, and DAG records. They are strictly intermediate reductions; the
   complex statement has no covering or cohomology claim, and the comparison stops before
   commuting tensor with homology. Verdict: pass.
4. Checked the proof route and imports against the DAG `proof` and `proof_deps`. The finite
   affine cover, affine-diagonal intersections, native Cech comparison, geometric comparison,
   and exact tensor steps are all used. No unused original dependency branch was removed from
   the interface, and the unit route `sk-prop-av-cube` remains represented. Verdict: pass.
5. Checked statement visibility and source provenance. Existing declarations retain their
   signatures and the new declarations have complete source/proof documentation and nodes;
   no duplicate library statement was found in repository searches. Verdict: pass.

Changed nothing during second reading; the delivered files already satisfy these checks.
