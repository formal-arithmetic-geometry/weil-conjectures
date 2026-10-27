## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.adicResidue_localModelComparison` by
composition of a local scalar-transport isomorphism, an explicit global model residue
calculation, and the constant-sheaf inverse-image and slice comparisons. The existing
statement is unchanged.

The private helpers prove the model calculation on the native pro-etale site, without
transporting its completed coefficients through an immersion or through AsSmall:
projective terms give flat completed constant terms, bounded-above flatness gives
K-flatness, the K-flat counit computes the residue, and uniqueness of scalar-extension
adjoints combines the two scalar extensions. The composite coefficient map is the
constant quotient by `CompletedConstantReduction.base_exists`. The existing ordinary
constant scalar comparison then gives the algebraic residue. Identity maps on additive
sections identify the normalized fixed-scalar restriction, and exact localization
removes all chosen representatives. The final proof applies the constant-sheaf pullback
and slice isomorphisms to that global calculation.

Added `Sheaf.Paper.ProEtaleLocalScalarDerivedIso`, containing only the generic locality
step that the preceding calculation needs. It compares two arbitrary local derived
objects after scalar extension to an arbitrary constant ring. It contains no completed
ring, ideal, perfect model, boundedness, finite-generation or residue calculation.
It is therefore strictly a part of the original argument, rather than that argument
under another name. Its source proof and zero-ring, empty-slice and unbounded edge
cases are recorded in its docstring and node.

Proof imports were added for scalar adjunctions, flat constant realization, bounded-flat
K-flatness, ordinary constant scalar extension, fixed-scalar normalization, and
constant-sheaf inverse image. No existing definition, public signature, exported attribute or
public import was changed. No other existing Lean module is adapted.

Validation: `lcompile.py --all` compiled both modules without warnings or errors.
The main module took 45.5 seconds and the new module 5.4 seconds, both below 60 seconds.
The original declaration signature was checked verbatim against the repository.
The existing node changes only `proof`, `proof_deps` and `proof_origin`; each node's
proof dependencies equal the union of its proof-step uses, and the new node's Lean
signature matches its module verbatim. No profiling options remain.

## Proved and sorry left

Original holes closed: `AlgebraicGeometry.Scheme.adicResidue_localModelComparison`.
There are zero holes left in the assigned module.

New hole: `AlgebraicGeometry.Scheme.proEtaleLocalScalarDerivedIso`, in
`Sheaf.Paper.ProEtaleLocalScalarDerivedIso`, node
`lem-sfb-proetale-local-scalar-derived-iso`.

This is one decomposition (one upper hole closed and one strictly simpler lower hole
added), not a net hole closure. All private model-calculation and normalization helpers
have complete proofs; no hole is in a definition or private declaration.

## No longer needed

No original public imports are removed: `AdicPerfectModelCompleteReduction` still
provides the algebraic residue appearing in the unchanged public statement.
Its theorem `adicPerfectModel_complete_reduction` is not applied: the proof calculates
the model residue directly at the native site and coefficient universes. The route also
avoids explicit completed-ring inverse-image normalization, so the assigned node no
longer directly uses `lem-weil-pbc-proetale-immersion-limit-preservation` or
`lem-pur-site-restriction-module-adjunction-exact`. Generic exact local restriction and
K-flat pullback are still needed by the new locality lemma; they have not been claimed
as globally pruned. The old direct proof dependency `lem-pur-derived-change-of-rings`
is now below that new node; the model proof uses the concrete scalar adjunction and
K-flat computation API of `BoundedConstructibleTower`.

The proof import of `AdicConstructibleTriangulated` was also removed: the proved
fixed-scalar normalization equivalence supplies exactness directly, so its
`fixedScalar_exact` helper is unnecessary. The assigned node no longer uses
`lem-sfb-adic-constructible-triangulated`.

Neither `ProEtaleLocalScalarHomologyIso` nor `SfbNormalizedLocalRestrictionIso` is
imported. The former concludes only additive cohomology isomorphisms, which cannot
supply the required derived isomorphism; the latter normalizes completed coefficients
but does not identify the fixed-scalar residue. No module or declaration is withdrawn.
Pruned modules: none. The unit route `sk-lem-integral-models` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan groups canonical derived scalar base change and fixed-scalar action
normalization into a sentence, but its declared generic change-of-rings theorem only
constructs scalar extension and its K-flat computation. It does not itself state the
locality comparison needed to apply the given local isomorphism. The new node records
that specific missing step. Existing additive cohomology locality is insufficient:
isomorphic cohomology sheaves alone do not give an isomorphism of derived objects.

The model calculation does not require Noetherianity, completeness of A, maximality
of I, finite generation of the terms, a lower bound, or immersion limit preservation.
The original public statement retains every hypothesis. The proof needs only an upper
bound and projective terms for this part.

## New nodes

`lem-sfb-proetale-local-scalar-derived-iso` is the scalar-transport step of the original
node, independently of the completed perfect-model calculation. It uses actual-ring
module inverse image, K-flat base change, slice restriction and normalization of constant
scalar actions. The assigned node's proof, proof dependencies and proof origin now
follow the implemented composition. No change record is needed because no existing
statement or definition changed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
