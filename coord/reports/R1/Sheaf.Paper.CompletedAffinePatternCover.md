## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffine_pattern_cover`
with its original signature. For each equivalence relation on the finite index set,
the proof directly takes the locus of within-class arrow equality and zero class
coefficient sums. These closed component-saturated loci cover because the actual
residue-field equality relation works at each point. Their canonical restrictions,
constructed using the existing `WContractification.Restriction` ring, form finite
pro-etale covers on affine opens. The generated sieve gives the requested local
relations and zero sums by the natural coefficient model.

Added the fully proved module `Sheaf.AlgebraicGeometry.ProAffineEtaleResidueEqualizer`.
Its stage argument pulls back the clopen diagonal of an absolutely affine etale
scheme. Open-immersion lifting proves equality of scheme morphisms, including on
nonreduced domains. Taking the intersection over limit stages gives the closed,
component-saturated residue equality locus and its universal equalizing property.
The two private covering helpers in the item are also fully proved.

Updated the item's proof record and added the geometric lemma's node. All added
imports in the item are private proof imports. No existing public import, definition,
instance, theorem signature, target, source-library file, or other consumer changed.
The blueprint unit route is preserved; its realization record is untouched.

## Proved and sorry left

Closed the original one of one holes:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffine_pattern_cover`
(node `lem-sfb-completed-affine-pattern-cover`).

Also proved `AlgebraicGeometry.proAffineEtale_residue_equalizer`
(node `lem-sfb-pro-affine-etale-residue-equalizer`) and its private stage equalizer
helper. Added zero holes. Neither delivered module contains `sorry`. This delivery
is a proof, not a decomposition. No arbitrary object is selected from an unproved
existence theorem: the restriction ring is the existing explicit colimit construction.

The complete sandbox compiled cleanly with `lcompile.py --all` (3.4 seconds for the
geometric module on its first successful compile, 6.3 seconds for the item).
After removing redundant imports, both modules compiled again in 2.9 and 6.2 seconds.
`#print axioms` for both public theorems returned exactly `propext`,
`Classical.choice`, and `Quot.sound`; the temporary diagnostic commands were removed.
The empty index set, empty scheme, repeated arrows, merged equality classes, and
nonreduced domains are included in the proof. There is no nonemptiness, reducedness,
or exact-pattern hypothesis hidden in the construction.

## No longer needed

The proof does not use the original direct dependency
`lem-pe-spectral-components-profinite`, module
`Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`. We do not construct
closures in a profinite component space: closed saturated loci descend through the
connected-component quotient by its quotient topology.

It also does not use the general canonical-localization dependency
`lem-pe-clopen-restriction-canonical-localization`, module
`Sheaf.RingTheory.ClopenRestrictionCanonicalLocalization`. The exact special
case needed is already supplied by the adopted source construction
`WContractification.Restriction`, its `indZariski` instance, and the proved
`Restriction.range_algebraMap_specComap` API
(node `lem-weil-pbc-restriction-spectrum-range`).

Those two edges were removed from this item's proof dependencies. There were no
pre-existing private proof imports to remove. No module is withdrawn: other
consumers may still need the two bypassed statements, and the adopted source tree
is preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

The proposed closure-of-exact-pattern-strata argument is unnecessary. Imposing only
the within-class equalities and zero class sums gives closed sets immediately and
still covers every point. Continuous p-adic functions are constant on connected
components; their Hausdorff property alone would not establish this saturation.

Pointwise equality of maps to an arbitrary scheme would be insufficient on a
nonreduced test scheme. The geometric lemma establishes the stronger fact actually
needed by factoring through the open equalizer at every etale stage. No statement
was disputed or changed. Searches of the current DAG and imported blueprint found
no existing statement of this pro-affine etale residue equalizer property; the
broader configuration-space equality-locus results concern different hypotheses.

## New nodes

`lem-sfb-pro-affine-etale-residue-equalizer`, in
`dag/nodes/sec-six-functors-basics/`, records the fully proved geometric lemma in
`Sheaf.AlgebraicGeometry.ProAffineEtaleResidueEqualizer`. It contains no coefficient
model, finite pattern family, or covering conclusion, and is strictly a geometric
part of the argument. Its three recorded searches were actually run through
`msearch.py`; their logs are in the sandbox's `searches.jsonl`. No change record is
needed because no existing statement, definition, public import, or interface changed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
