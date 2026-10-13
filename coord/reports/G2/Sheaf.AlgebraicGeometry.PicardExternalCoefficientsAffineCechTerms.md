## What changed

Proved `AlgebraicGeometry.Scheme.Modules.picardAffineCech_normalized_terms`, with its
signature and every existing definition unchanged. The proof constructs the native
Cech scalar-coordinate linear equivalence, applies `TensorProduct.piLeft` to the
finite tuple set, composes the chart additive equivalences, and proves the specified
pure-tensor normalization. No covering or differential hypothesis was added.

Added `Sheaf.AlgebraicGeometry.ExternalTensorAffineOpenSections`, with the proved
single-chart theorem `externalTensor_affine_open_sections` and its explicit pure
section construction. It uses the affine pushout-section comparison on the original
product square, the two affine projection-pullback section comparisons, pushout
algebra tensor cancellation, and the affine tensor-section comparison. This avoids
transporting external coefficients through pullback-composition and tensor
isomorphisms. The private pushout tensor algebra calculation reuses the proof from
`ExternalGlobalSectionsTensorAffine`; its helper there is private, so it cannot be
imported and applied. No definition chooses an arbitrary object from an unproved
existence theorem.

The new proof imports are private. The second reading removed the redundant public
`Mathlib.AlgebraicGeometry.Morphisms.Affine` import from the new chart module;
the required affine-open signature vocabulary remains publicly available through
`FieldLinearModuleCohomologyOperations`. The item imports the chart theorem and
`Mathlib.LinearAlgebra.TensorProduct.Pi`, replacing its old affine-global-sections
proof import. Updated the item's proof route and added the single-chart node.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.picardAffineCech_normalized_terms`
(node `lem-sc-picard-external-coefficients-affine-cech-terms`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.externalTensor_affine_open_sections`
(node `lem-sc-external-tensor-affine-open-sections`).

There are no sorries left in either delivered module and no new holes.
The statements imported from the existing library retain their existing proof
status; this delivery does not claim that their entire dependency closure is closed.

Edge cases: the tensor/product equivalence handles an empty tuple set; the affine
product and section comparisons allow empty A and V, including zero coordinate
rings; all formulas allow zero coefficients. The argument needs only the stated
finite index type and affine intersections, never a cover or affine diagonal.

## No longer needed

Removed the redundant public import `Mathlib.AlgebraicGeometry.Morphisms.Affine`
from the new chart module. Retained the item's existing public Affine export to
preserve the existing interface used by downstream modules.

Removed the item's proof import
`Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine`.
Its node `lem-sc-external-global-sections-tensor-affine` is no longer used by this
proof. The direct appLE chart calculation also does not use the old planned nodes
`lem-weil-pbc-module-pullback-tensor` and
`lem-weil-pbc-open-immersion-module-pullback-restriction`; no import of
`Sheaf.AlgebraicGeometry.ModulePullbackTensor` is needed for this argument.
The affine fibre-product ring calculation is still needed, now inside the new
chart node. These are pruning claims for this proof route, not claims that other
targets or modules no longer use those results.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old route proposed transporting the external
coefficient to a product of restricted schemes. A shorter direct chart computation
uses existing affine appLE pullback-section statements and the affine section
pushout comparison, whose pure-tensor formulas already use the original projection
units. This preserves the intended affine-chart calculation and the unit route.

The unit record `sk-prop-av-cube` has no realization binding to this node; the
change is below the unit level. Read Stacks Tag 0BED, `varieties-lemma-kunneth`,
the affine-open paragraph and displayed equality of Cech complexes. Read the
existing affine section and tensor-section declarations before implementing the
chart calculation. LeanSearch returned HTTP 500; LeanFinder, Loogle and Mathlib
source searches ran and are recorded in `searches.jsonl`.

## New nodes

`lem-sc-external-tensor-affine-open-sections` records the normalized section
comparison for a single affine product open. It has no Cech complex, tuple family,
finite-index hypothesis or differential assertion. Its full proof is delivered in
`Sheaf.AlgebraicGeometry.ExternalTensorAffineOpenSections`; no hole was split off.
No interface changes or forced adaptations were necessary.

## Second reading by G2

1. Compared the item against the repository with `diff -u`: every existing
   declaration signature and definition body is unchanged. Only the original
   theorem proof, its proof description, imports and a private coordinate helper
   changed. The new chart module contains a real section construction; no
   statement or definition change record is needed.
2. Compiled both modules independently through `lcompile.py`, without errors or
   warnings. Searched both sources for sorry and forbidden declarations: none.
   Scratch copies with `#print axioms` show exactly `propext`, `Classical.choice`
   and `Quot.sound` for both public theorems. The chosen adjunction has its unit
   fixed sectionwise by `exists_tensorPullbackAdjunction`; the choice is not an
   arbitrary witness of mere existence. The chart equivalence is constructed
   from actual linear equivalences and bijective section comparisons.
3. No statement was split off with a hole. Read the new chart theorem and its
   complete proof, including scalar-map naturality, the pushout base transport,
   pullback linearity, quasi-coherence and the pure-tensor formula. It is strictly
   smaller than the Cech term theorem. Empty opens, zero modules and empty tuple
   families require no additional hypothesis. Independent LeanFinder, Loogle and
   source searches confirm `TensorProduct.piLeft` supplies the finite-product
   step; related existing external-section theorems do not give this normalized
   two-open chart statement directly.
4. The proof assembles chart equivalences using the existing finite-product
   theorem, rather than adding a lower hole. Checked the old proof dependencies
   against the report: all bypassed dependencies are named; the affine
   fibre-product calculation remains within the chart proof. The unit record
   `sk-prop-av-cube` has no realization attached to this item, and its theorem
   and steps are unchanged. Removed the redundant public Affine import from
   the new chart module after compiling scratch copies without it. The item's
   existing export remains: the first dry run required a change record for
   removing it, so that interface change was withdrawn. A scratch test
   removing the private Tilde import failed at the quasi-coherent pullback
   instances, so that proof import is necessary and retained.
5. Read both delivered node records against their Lean declarations: the new
   statement is verbatim, all required new-node fields are present, and the
   proof steps and dependency unions describe the implemented chart calculation
   and finite-product assembly. No change to the unit record is needed.

Second reading changed only the redundant Affine import in the new chart module
and this report. Independently checked [Stacks Tag 0BED](https://stacks.math.columbia.edu/tag/0BED),
the affine-open paragraph and its displayed equality of Cech complexes.
No proof repair or additional hole was necessary.
