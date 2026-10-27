## What changed

Filled `AlgebraicGeometry.unramifiedLocus_baseChange` without changing its signature or the
construction `unramifiedLocus`. All auxiliary lemmas are private and completely proved.
The base-change argument follows Stacks Tags 0475 and 02GF using finite differential-module
support: residue-field tensor products detect support, their nontriviality is preserved by field
extension, and the differential module commutes with an affine pushout. Affine neighbourhoods
then identify the actual scheme stalk maps with localizations of the ring maps.

For the final residue-map characterization, apply the existing maximal-ideal/residue criterion
on the original morphism. The proved fibre-stalk quotient theorem turns its maximal-ideal
condition into injectivity of the fibre residue map. This avoids transporting the finite and
separable extension predicates between different residue-field presentations.

Added proof imports of `Sheaf.AlgebraicGeometry.FibreStalkQuotient`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood`, and Mathlib's
Kahler tensor-product, faithfully flat, vector-space basis, local-ring module, unramified
locus, and affine-pushout APIs. Updated the existing node's proof, proof dependencies, proof origin, and obsolete tool use.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.unramifiedLocus_baseChange`
(node `lem-trf-unramified-locus-base-change`). Added zero holes and split off zero statements.
Validation: the complete final module compiled through `lcompile.py` with exit code zero,
no errors or warnings, in 9.2 seconds. The source signature and definition body were compared
against the library and are unchanged; import-direction checks passed for both added project
dependencies.
There are zero textual `sorry`s in the delivered Lean module. The proof still uses the existing
statement `AlgebraicGeometry.unramified_neighbourhood_iff_maximalIdeal_residue` from
`Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion`, whose existing hole is unchanged
and belongs to node `lem-trf-unramified-maximal-ideal-residue-criterion`.

## No longer needed

Removed proof import `WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`.
Its node `lem-weil-pbc-unramified-base-change-open` is not needed by this proof: affine
base-change of differential-module support proves both inclusions at once. Removed that node
from this item's `proof_deps`, proof-step uses, and `tool_uses`; no source-library declaration or
module is withdrawn. The node `lem-weil-pbc-lft-base-change` remains needed through Mathlib's
locally-finite-type pullback instance. No other dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The old first step cited Tag 0475 as prose, but its sole declared dependency proved only
preservation of global unramifiedness, not the converse pointwise base-change implication.
The delivered private lemmas supply that argument from Mathlib. The old second step proposed
applying the maximal-ideal criterion to the fibre and transporting the residue-field extension.
Applying it directly to the original morphism and using the existing fibre-stalk quotient
proves the same unchanged clause more directly. No statement or definition repair was needed.
The unit record `sk-i-curve-zero` has no realization entry for this auxiliary node; its fixed
statement and steps are preserved. Both added project dependencies are already proved, generic
tools (a source neighbourhood from a stalk, and the canonical fibre-stalk quotient).

The empty source and empty fibres cause no extra cases: every pointwise argument starts from
an actual point. The support argument requires only finite generation of the differentials,
which follows from local finite type; it uses no flatness or finite presentation hypothesis.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
