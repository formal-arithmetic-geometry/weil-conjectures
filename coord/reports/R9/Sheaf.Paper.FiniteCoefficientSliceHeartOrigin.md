## What changed

Filled `AlgebraicGeometry.Scheme.finiteCoefficient_slice_heart_origin` without
changing its signature, definitions, or public imports. All changes are confined
to the item module and its DAG node.

The proof first cancels ordinary scalar extension against restriction along the
coefficient isomorphism, using the existing scalar adjunction and uniqueness of
left adjoints. The existing constant-scalar sheafification comparison identifies
the actual Koszul constant realization with the fixed-coefficient constant sheaf.
Applying these comparisons on a ringed slice transports each given local model.
Weakly etale slice localization then gives constant models on the source schemes.

Only `hloc V (identity V)` is needed: the covering-sieve point criterion chooses
one trivializing chart through each point of `V.left`. These charts form an etale,
hence proetale, covering. The proved `etale_origin_of_finite_models` supplies a
finite locally constant etale origin and the comparison marking. The proved
`local_finite_module_models` helper restricts its finite models to every etale
chart in the exact covering-family form requested by the conclusion.

The new proof-only imports are `Sheaf.Paper.BoundedConstructibleTower`,
`Sheaf.Paper.ProEtaleOriginFromFiniteModels`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicLisseFixed`,
`Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence`.
The two `import all` lines reuse existing proved private helpers rather than
restating their obligations.

Private helpers contain complete proofs. No existing definition or shared
interface is changed and no source-library file is modified.

Validation: the full item compiled through `lcompile.py` in 15.9 seconds with
exit code zero and no warnings. The unchanged statement contains an unused
binder `g` inside `hloc`; its unused-variable warning is suppressed only for
this theorem, preserving its exact signature. All added imports are used.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finiteCoefficient_slice_heart_origin`
(node `lem-weil-pbc-finite-coefficient-slice-heart-origin`).

There are zero remaining sorry declarations in the item, zero holes added,
and zero split-off statements. This is a proof, not a decomposition.

## No longer needed

No original public import is removed and no module is withdrawn. The original
proof dependencies all remain needed: constant scalar encoding, coordinate
restriction, weakly etale localization, and finite-model descent. The encoding
node is now a transitive dependency through the restriction construction and
constant-scalar comparison; it is not claimed as globally pruned.

The descent input needs only the cover over `V`, rather than every cover over
all further charts. The local families in the conclusion follow from finite
local constancy of the descended etale sheaf. No new derived-origin theorem,
complex transport theorem, cohomological bound, or noetherian hypothesis is
needed. The blueprint unit's realized statement and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The existing proved scalar adjunction,
constant-scalar comparison, slice equivalence, finite-model descent, and finite
local-value APIs suffice to close the obligation. No further split is needed.

Empty charts are handled by the empty point-indexed cover. Finite modules over
the finite coefficient ring have finite underlying sets, and universe lifting
preserves this finiteness. The zero ring and zero module require no exceptions.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
