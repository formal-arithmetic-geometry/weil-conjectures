## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.exists_lift_section_of_fiber_h1_eq_zero`
by a complete assembly proof with its original signature. It uses a section-normalized
finite free complex over the base stalk, transports the given first fibre cohomology
vanishing to that complex, applies the proved local algebra theorem, and represents the
resulting pushforward germ by a section on an open neighbourhood. The comparison formula
then proves the required equality for actual tensor pullback of that section.

Added `Sheaf.Algebra.Homology.LocalResidueCohomologyLifting`. Its canonical residue complex
and reduction map use the scalar-extension/restriction unit. The main theorem proves
surjectivity on zeroth cohomology from first residue cohomology vanishing. The proof uses
the adopted, already-proved minimal-complex theorem, proves that minimal residue
differentials vanish, applies Nakayama to degree one, lifts residue vectors by tensor
induction, and transports the result through the homotopy equivalence using naturality.

Added `Sheaf.AlgebraicGeometry.ProperFlatSectionNormalizedStalkComplex` for the geometric
model and its section normalization. This statement has no cohomology-vanishing
hypothesis and asserts no section lifting. It is the geometric comparison part of the
original argument, strictly separate from the proved local algebra and germ assembly.
No data definition chooses a witness from this unproved existence statement: the
witnesses are eliminated only inside the proof of the original theorem.

Updated the item's proof, proof dependencies and proof origin. Recorded the exact
already-proved adopted minimal-complex theorem as a new DAG attachment; its source file
is unchanged. No existing interface, instance or other module was changed. Edge cases
checked mathematically: arbitrary nonclosed s, nonreduced local rings, empty fibre,
zero degree-zero or degree-one terms, and a zero prescribed section.

Validation: `lcompile.py --all` compiled all three delivered modules without warnings.
The local algebra took 5.8 seconds, the geometric statement 3.8 seconds, and the item
5.1 seconds, all below the per-file limit. All node dependencies resolve, proof dependency
lists equal the unions of the proof steps, and all Lean lines have at most 100 characters.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_lift_section_of_fiber_h1_eq_zero`
(node `lem-sfb-proper-flat-fibre-section-lifting`). The item originally had one hole and
now has zero.

Proved without new holes:
`CochainComplex.surjective_residueCohomologyMap_zero`
(node `lem-sfb-local-residue-cohomology-lifting`), including its private supporting lemmas.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.exists_section_normalized_stalk_complex`
(node `lem-sfb-proper-flat-section-normalized-stalk-complex`). Its full proof in words and
sources are in its docstring and node. This is a decomposition: one original hole closed,
one strictly intermediate geometric comparison hole added, net zero holes closed. The
finite-complex local algebra and final section construction are complete Lean proofs.

`CochainComplex.exists_homotopyEquiv_isMinimal`
(node `lem-sfb-local-finite-free-minimal-model`) is an existing proved source declaration;
this delivery only attaches its node and adds no Lean declaration or hole for it.

## No longer needed

Removed the following proof imports from the item, replacing them with the normalized
stalk-complex module:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange`
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`
- `WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits`
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
- `WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
- `WeilConjectures.Algebra.Homology.UnitEntrySplits`
- `WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap`
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`

Most of these declarations remain prerequisites in the geometric comparison node's
proof plan; removing their direct imports is not a claim that their mathematics is
unneeded. The adopted minimal-complex theorem proves its own idempotent cancellation construction
from Mathlib; it does not use the old `UnitEntrySplits` module or its holed theorem.
Existing generic-tool approvals on the parent are preserved.

The new argument works over the local ring and represents a germ at the end. It avoids
explicit principal-neighbourhood finite-free spreading and denominator-product
shrinkings in the item. In particular
`lem-weil-pbc-finite-projective-prime-local-free` and its module
`WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree` are not required by this
route: finite projective modules over the local ring are free directly. Also
`lem-weil-pbc-free-complex-unit-entry-splits` and
`WeilConjectures.Algebra.Homology.UnitEntrySplits` are replaced by the already-proved
minimal-model construction. Other users may still need these modules. No module is withdrawn, and no adopted source declaration or
public import is removed. The unit and chapter routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan's canonical comparison needs more than unrelated cohomology
isomorphisms. The current adopted `exists_isFiniteFreeComplex_higherDirectImage` explicitly
states in its docstring that its comparisons are noncanonical and insufficient for
canonical base-change assertions. The recorded perfect-base-change declaration combines
those comparisons with a canonical Cech comparison, but does not itself identify the
finite free comparisons with that canonical map. Also the affine sections declaration
uses the source `Scheme.Modules.H`, whereas the item uses
`RingedSpace.moduleCohomology`. The new geometric comparison node makes both the
normalization and this cohomology bridge explicit, citing the existing natural
module/source comparison. None of this disputes the mathematical section-lifting
statement.

## New nodes

`lem-sfb-local-residue-cohomology-lifting`: the proved local-ring algebra theorem,
with the canonical residue complex and cohomology reduction map. It supplies the
original steps 4-6 through a minimal model over the local ring.

`lem-sfb-proper-flat-section-normalized-stalk-complex`: the remaining geometric model
comparison, encompassing the original geometric-model and actual restriction
identifications. It has no vanishing or lifting conclusion, and its proof plan names
the existing geometric dependencies and the module/source cohomology bridge.

`lem-sfb-local-finite-free-minimal-model`: an attachment to the exact existing theorem
`CochainComplex.exists_homotopyEquiv_isMinimal` in the adopted source. It adds no module,
no declaration and no hole. It is the generic algebra tool already available for the
minimal-model step; no new source-library interface is introduced.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
