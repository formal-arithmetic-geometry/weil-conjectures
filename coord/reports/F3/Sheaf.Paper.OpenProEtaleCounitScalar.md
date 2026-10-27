## What changed

Proved the three theorems of `Sheaf.Paper.OpenProEtaleCounitScalar`, preserving their
signatures and the four public definitions. The proof combines the declared etale
flat-model domains, actual unbounded open adjunction transport, coefficient/site square,
and scalar/pullback cube. Private generic calculations transport counits through exact
restriction coordinates and paste the comparison squares.

The current library already proves the etale balancing comparison and its open-unit
normalization. Private proof imports of `EtaleOpenCounitFlatModels` and
`EtaleOpenScalarExchange` expose those proved helpers using `import all`. The prescribed
inverse mate agrees with the balancing isomorphism by its adjunction transpose. Local
irreducibility keeps the derived localization constructors abstract during elaboration.
The node's proof, proof dependencies, and proof origin follow this implementation.

## Proved and sorry left

Closed all three original holes (3 closed, 0 added):

- `AlgebraicGeometry.ProEtale.openProEtaleCounitScalar`.
- `AlgebraicGeometry.ProEtale.openProEtaleCounitScalar_site`.
- `AlgebraicGeometry.ProEtale.openProEtaleCounitScalar_transport`.

Remaining local holes: none. No statements are split off. The complete module compiled
through `lcompile.py`; delivery runs the server compilation and required preflight.

## No longer needed

Removed direct imports of `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`,
`Sheaf.Paper.MateOpenRestriction`, and `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
the proof does not directly use their declarations. Other retained imports may still
reach these modules. No module or declaration is withdrawn.

Removed the draft's direct proof import and proof dependency
`Sheaf.Paper.EtaleDirectImageScalarComposition` /
`lem-pur-etale-direct-image-scalar-composition`: its identity-factor computation is
already supplied by the proved flat-model helper. It remains a transitive dependency
of that helper. The direct inverse-mate expansion and the duplicated identity scalar
calculation are unnecessary. The flat-model theorem is retained for its finite-Tor
domains and etale origin; representative calculations are unnecessary in this assembly.
The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The interrupted draft duplicated etale normalization
calculations whose proofs have since become available in the current library. Reusing
these proved helpers closes those steps. The derived counit calculation is performed
for abstract exact functors first, then specialized to the sheaf categories; this
avoids repeatedly unfolding the sheaf adjunction constructors.

The canonical compact-support site comparison and fixed comparison agree after
inclusion in the ambient categories. Exact composition/isomorphism inclusion formulas
and naturality of the bounded-below direct-image comparison prove that equality.
Both proper identity factors are removed with the actual canonical derived identities.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
