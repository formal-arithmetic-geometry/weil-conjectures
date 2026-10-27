## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.proEtaleLocalScalarHomologyIso` by a
proof using the actual scalar-extension and local-restriction functors. All added
helpers are private and proved. The existing public statement and public import
are unchanged.

The proof identifies the identity-coefficient pullback with module inverse image,
compares ordinary scalar extension with inverse image and slice restriction, and
descends the comparison using flat-term K-flat resolutions and their computation
counits. Applying local scalar extension to the supplied isomorphism and commuting
homology with the exact local functor gives the required additive-sheaf isomorphism.
The slice comparison uses the sectionwise tensor construction and the existing
slice/sheafification isomorphism. The inverse-image comparison uses uniqueness of
left adjoints to the natural coefficient square of right adjoints.

The global adjunction and computation counit reuse the normalized API in
`Sheaf.Paper.BoundedConstructibleTower`. The private slice derived-pair interface
retains the full left-derived universal property, shift and triangulated structure,
and K-flat computation from the generic change-of-rings theorem. Thus the selected
pair is determined up to its counit-compatible isomorphism.

The copied DAG node records these steps and their dependencies. The proof-context
record is `coord/changes/Y2-proetale-local-scalar-proof-context.md`. The proof has no
boundedness, perfection, completeness, or immersion hypothesis. Identity coefficient
maps, zero rings, empty slices, and unbounded objects are included by the same
construction.

Verified with `lcompile.py`: the complete module compiled without warnings in 54.6 seconds.
The public signature is textually identical to the original, the delivered module has zero
`sorry` occurrences, every Lean line is at most 100 characters, and the added direct proof
imports passed the import-direction check.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.proEtaleLocalScalarHomologyIso` (the item's only
original hole). Added holes: none. No `sorry` remains in the delivered Lean source;
there are no split-off statements.

## No longer needed

No original import is removed and no module is withdrawn. No pruning is claimed.
The K-flat inverse-image step uses the existing private helper in
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`;
`Sheaf.Paper.KFlatRingedToposPullback` remains a transitive dependency and needs no
direct proof import.
The generic derived tensor/pullback theorem
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is not applied directly: the
proof constructs the needed scalar-extension comparison through adjunctions and
K-flat counits. Its module remains a transitive dependency of the reused scalar
comparison infrastructure, so this is not a claim that its declaration or module
can be removed. All unit-route statements remain attached and unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original resolution plan
is valid; the missing work was the ordinary comparisons, their descent, and the
representative-normalization glue. Imported specialized site-size and slice-derived
instances require temporary exclusion to avoid phantom-universe inference. These
proof-local exclusions and explicit universe choices do not change any library
definition or target statement. No other module is adapted.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
