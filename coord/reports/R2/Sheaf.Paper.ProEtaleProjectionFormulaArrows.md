## What changed

Filled the proofs of `AlgebraicGeometry.Scheme.proEtaleStrictPerfect_flat` and
`AlgebraicGeometry.Scheme.proEtaleMixedTensor_existsUnique` in
`Sheaf.Paper.ProEtaleProjectionFormulaArrows`. All existing signatures and constructions
are retained. Proof-only imports provide independent-universe bounded-flat K-flatness,
tensor colimits, flat resolutions, and compatibility of tensor with mapping cones.

Validation: the resumed module compiled through `lcompile.py` in 48.7 seconds with
exit code 0 and no warnings.

Strict-perfect terms are retracts of finite products of the tensor unit, hence flat.
The existing bounded-above criterion gives K-flatness. For the mixed comparison, use
the reduced functorial flat resolution and the model's representative isomorphism.
Tensoring a quasi-isomorphism with the given K-flat coefficient is a quasi-isomorphism,
by the mapping-cone criterion. Naturality of the resolution and representative
isomorphism proves normalization for every resolution; cancellation proves uniqueness.

## Proved and sorry left

Closed two original holes (not a decomposition):
`AlgebraicGeometry.Scheme.proEtaleStrictPerfect_flat` and
`AlgebraicGeometry.Scheme.proEtaleMixedTensor_existsUnique`.
No holes added and no split-off statements.

One original hole remains:
`AlgebraicGeometry.Scheme.proEtaleProjectionUnit_existsUnique`
(node `def-weil-pbc-projection-formula-arrows`). It requires comparison of the canonical
ordinary pro-etale tensor map with scalar multiplication on the coefficient unit.
The existing source and complete proof in words remain at that theorem.

## No longer needed

No original imports removed and no module withdrawn. The existing public imports
remain necessary for the published interface and the specified finite-total inverse.
The legacy bounded-above flat-site theorem identifies site and coefficient universes;
the proof instead uses the existing independent-universe bounded-flat theorem.
No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt did not compile: representative naturality needed explicit
full-subcategory and product-functor simplification, product morphisms needed
componentwise comparison, and the final composition needed associativity and the
identity functor map equation. These are repaired without changing statements.
The node is a definition with no proof steps; the completed arguments follow its
specified flat K-flat and mixed representative constructions.


The resumed session rechecked the retained file against current shared sources and
compiled it successfully. An earlier preflight flagged a file-level `open scoped ZeroObject`
as an interface command; the proof now supplies a local zero-object instance instead.
The unit-normalization theorem at independent site universes
exists in `Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses`, but applying
it also requires constructing an algebraic lift and identifying its generalized
pure-tensor comparison with the pro-etale adjunction-unit characterization. No such
identification is supplied by the existing pro-etale interfaces; this remaining
argument has not been replaced by a new hole or an arbitrary chosen comparison.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
