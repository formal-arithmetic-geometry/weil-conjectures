## What changed

Implemented the proof of
`AlgebraicGeometry.regular_normal_and_normal_decomposition` without changing its signature.
Regular affine charts give normal stalks using `IsRegularRing.isNormalRing` and the canonical
localization equivalence. The already proved source-library theorem
`Scheme.exists_isClopen_isIntegral_of_isIntegrallyClosed_stalk` supplies the finite normal
integral clopen decomposition. The proof identifies those pieces with all irreducible
components using maximality and `IsPreconnected.subset_isClopen`, and obtains the coproduct
universal property for their actual inclusions using `nonempty_isColimit_cofanMk_of`.
The final connected case uses the proved `irreducibleSpace_of_isDomain_stalk`.

Added the proof-only import `WeilConjectures.AlgebraicGeometry.NoetherianComponents` and
updated `rem-pc-regular-normal` to record this shorter route. All original public imports
and every existing declaration signature are retained. The Jacobian unit has no proof steps
in its `realized` record, so this route does not bypass a unit step.

Validation: the resumed `lcompile.py` run compiled the module cleanly in 3.3 seconds.
The import-direction check confirms that the new source-library import creates no cycle.
Earlier attempts received no answer from the compile server; the resumed run resolved that
service interruption. The delivery dry run subsequently compiled the proof, passed the
axiom check and server preflight, and printed OK (review class CODEX: node-file change).

## Proved and sorry left

The sandbox replaces the sole original hole in
`AlgebraicGeometry.regular_normal_and_normal_decomposition` (node `rem-pc-regular-normal`)
with a complete, compiler-checked proof. Closed: 1 of 1 original holes, namely the
declaration above. Remaining: none (zero `sorry` tokens in the module). Added: zero holes
elsewhere. No statements were split off.

## No longer needed

Removed these proof-only imports:

- `Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`.
- `Mathlib.AlgebraicGeometry.FunctionField`.
- `Mathlib.AlgebraicGeometry.Gluing`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` (the hypothesis already states affine-open
  regularity using the publicly imported Mathlib ring predicate).

The following former direct proof dependencies are unnecessary for the shorter proof:

- `def-pc-reduced-scheme`.
- `lem-weil-pbc-affine-open-spec-points` (the stalk-localization API already supplies
  the prime used in the first clause).
- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`.
- `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`.
- `lem-weil-pbc-finite-affine-coproduct-spectrum`.
- `lem-weil-pbc-spec-domain-stalks-function-field`.
- `lem-weil-pbc-localization-normal-domain`.
- `lem-sc-components-open-injection`.
- `lem-sc-irreducible-components-cover`.
- `lem-weil-pbc-noetherian-finitely-many-components`.
- `def-weil-open-immersion`.
- `lem-weil-pbc-scheme-morphism-gluing`.

These are removed as direct dependencies of this node; this does not assert that they
are absent from all transitive imports or unused by other targets. The obsolete top-level
`tool_uses` entry for `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`
is withdrawn. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original seven-step affine-product route is mathematically valid but unnecessary:
the source library already proves the required finite normal integral clopen decomposition
and the connected domain-stalk irreducibility criterion. No statement correction or change
to a definition is needed. The existing declaration docstring retains the literature's
longer proof plan; the node now records the shorter proof script.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
