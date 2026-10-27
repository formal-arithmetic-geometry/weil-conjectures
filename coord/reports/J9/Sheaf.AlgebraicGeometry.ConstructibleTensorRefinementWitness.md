## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.ConstructibleTensorRefinementWitness`.
The canonical comparison and all declaration signatures are unchanged. Naturality follows
from oplax tensorator naturality and naturality of the two composition comparisons.

For the witness theorem, extend the given stratifications by their assumed constructibility
fields, and use their actual fibre-product refinement. Pullback stability supplies the two
finite locally constant factors. The proved source-library local-constancy and finite-stalk
tensor lemmas supply their tensor. Transfer across the specified canonical comparison, then
use the finite constant-value characterization to witness constructibility on that refinement.
Single-file validation through `lcompile.py` passed without warnings (11.2 seconds on resumed validation).
Updated the existing node's proof, proof dependencies and proof origin accordingly. Added only
a private proof import of `WeilConjectures.ConstructibleSheaf.MonoidalParts`.

## Proved and sorry left

Closed 2 of 2 holes, both attached to
`lem-fd-constructible-tensor-refinement-witness`:

- `AlgebraicGeometry.Scheme.constructibleRefinementTensorIso_naturality`.
- `AlgebraicGeometry.Scheme.constructible_tensor_refinement_witness`.

No holes remain in the item; no holes or declarations were added elsewhere. No decomposition.

## No longer needed

Removed these private proof imports:

- `Sheaf.AlgebraicGeometry.FiniteTypeConstantModulePullback`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

The direct proof no longer cites these former proof dependencies:
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-sfb-finite-type-constant-module-pullback`,
`lem-weil-pbc-etale-base-change-continuous`,
`lem-weil-pbc-etale-base-change-finite-limits`, `def-weil-size-convention`,
`lemma-constructible-pullback-constant`,
`def-weil-pbc-finite-type-locally-constant-module-sheaf`,
`def-weil-pbc-etale-site`, `lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
`lem-pc-sites-module-sheafification-tensor`, and
`lem-weil-pbc-etale-inverse-image-restriction`.
Their obsolete top-level tool-use approvals were removed from this node.

The existing finite locally constant pullback theorem subsumes the explicit local-model
pullback construction. The two tensor lemmas subsume the common-cover tensor calculation.
These lower ingredients may still be used transitively by the source-library proofs or
elsewhere; this delivery withdraws no modules or declarations. Existing public imports are
preserved as the published interface, including the coefficient inverse-image statement
import. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The detailed DAG route is longer than necessary: the source library already proves finite
locally constant pullback stability and the two tensor components. Its partition lemma uses
`Stratification`, which includes constructibility, while the input structure omits that field;
the assumed hS and hT fill it without changing the schemes, maps, indices or subsets.
Empty strata and zero-stratum partitions require no choices of points or nonempty strata;
the partition and all finite-value conversions work uniformly. No hypotheses were changed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
