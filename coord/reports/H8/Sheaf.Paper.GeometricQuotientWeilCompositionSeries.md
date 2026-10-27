## What changed

Proved `RealSheaves.geometricQuotientWeilCompositionSeries` in
`Sheaf.Paper.GeometricQuotientWeilCompositionSeries`, preserving its statement,
all existing definitions, instances and public imports. A declaration-local
unused-variable linter setting permits the two redundant hypotheses to retain
their exact original binder names. Four proved private
helpers implement the image-quotient isomorphism, zero-stalk reflection, the
actual stalk intertwiner, and geometric-to-Weil irreducibility.

The proof uses the normalized realization and its full-faithful Hom dictionary.
It constructs the prescribed image chain, proves all maps to the final stalk
injective by reverse finite induction, and applies the first isomorphism theorem
to each prescribed quotient map. The quotient equivalence retains the required
formula on representatives. Irreducible quotients give covers, hence the chain
is a composition series of exactly the prescribed length; their inverse
subquotient equivalences prove the constituent assertions. No splitting is used.
The construction includes the empty filtration without a special assumption.
Single-file compilation through `lcompile.py` succeeded in 16.5 seconds after
removing the unused private imports; the delivery preflight checks the final
file and its declaration probes.

Updated the existing node's proof, proof dependencies and proof origin to this
argument. No existing declaration signature, target statement, or definition body changed.

## Proved and sorry left

Closed one existing hole: `RealSheaves.geometricQuotientWeilCompositionSeries`
(node `lem-zl-geometric-quotient-weil-composition-series`).

Added zero holes. Zero holes remain in the delivered module. No statements were
split off. The imported fundamental-representation and Hom-dictionary results
are the project's existing stated dependencies, not new holes in this delivery.

## No longer needed

Removed the private imports `Sheaf.Paper.EtaleWeilSheafEquivalence` and
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`.
Replaced the former with the smaller `Sheaf.Paper.EtaleWeilRealization` import.
The generic representation operations used here already come from the existing
public composition-series import.

The proof no longer depends on
`prop-wf-weil-sheaf-representation-equivalence`: the hypothesis `hexact` already
provides the required stalk exactness, and full faithfulness of the normalized
realization suffices to reflect zero. Essential surjectivity, reconstruction,
abelian transfer and tensor compatibility from the broader equivalence are not
needed for this argument. Removed the obsolete top-level `tool_uses` approval
of that node; the two replacement realization/Hom nodes are smaller dictionary
subresults in the same generic-tool role, and do not change the unit route.
No claim is made that these modules are unused by other items globally.

All other original declared dependencies remain: fundamental/geometric action,
the composition-series definition, and the constituent operations.

## Where the brief, the DAG or earlier work was wrong

The original plan invoked exactness of a full tensor equivalence even though the
Lean statement already assumes injectivity, exactness and surjectivity at every
geometric stalk. The implementation specializes this hypothesis to the supplied
point and uses only the normalized realization Hom dictionary for equivariance,
functoriality and zero reflection. The existing generic-point and monomorphism
hypotheses are retained verbatim; no stronger hypotheses are added.

The zero-length case works because the sole map to the final term is its
identity, while zero reflection makes its image zero. For positive length,
nonzero quotient stalks ensure strict covers, including nonsplit filtrations.
No mathematical error or false statement was found.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
