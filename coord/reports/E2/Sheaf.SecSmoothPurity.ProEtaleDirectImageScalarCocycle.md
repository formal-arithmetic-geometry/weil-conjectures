## What changed

Replaced the single sorry in `Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle`
with the direct normalized-mate argument. The theorem signature and its four public imports
are unchanged. All auxiliary declarations are private and proved in the same module.

The proof identifies the specified scalar associator with adjunction composition using the
existing derived Hom comparison and successive-derived-quotient representative formula.
It proves ordinary coefficient restriction/pullback coherence by transposing to comparisons
that are identity on sections, derives that square using the proved exact-functor pasting
lemma in the adopted source library, and takes scalar adjunction mates. A generic counit
calculation then proves the required direct-image equation. The unit's associativity route
is preserved. There are no changes to definitions, other modules, or public statements.
The node's proof, dependencies and proof origin describe this argument.

Change record: `coord/changes/proetale-direct-image-scalar-cocycle-proof-context.md`.
The first preflight required this record for new local elaboration commands. Their
attributes are local; the public theorem signature is unchanged. The downstream source
check found zero current Lean importers, and no consumers required adaptation.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.proEtaleDirectImageScalarCocycle`
(node `lem-sp-proetale-direct-image-scalar-cocycle`): 1 of 1 original holes.
Added: zero holes. Remaining in the delivered module: none. Split off: none.
Every private helper has a complete proof; no new public theorem or DAG node was introduced.
This is a proof from existing declarations, not a decomposition into admitted statements.

Validation: the complete module compiled on the project server without diagnostics in
33.9 seconds. The theorem signature was compared with the current shared source and is
identical; the delivered Lean file has zero literal `sorry` occurrences. All lines are
at most 100 characters.

## No longer needed

Removed direct imports:

- `Sheaf.Paper.RingedCoefficientProjectionCocycle`: the general ringed-topos cocycle is
  replaced by sectionwise restriction coherence and composition of the actual mates.
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`: no constructible or bounded
  category interface occurs in this ambient unbounded proof.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the needed public definitions are
  already reexported by the existing public imports.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the proof uses the
  already normalized derived composition API; it constructs no fresh resolution.
- `Mathlib.CategoryTheory.Adjunction.Basic`: already reexported by the remaining imports.

The node no longer directly depends on `lem-pur-ringed-coefficient-projection-cocycle`
or `lem-pc-kflat-resolution`; their obsolete top-level tool approvals are removed,
with the remaining approvals kept in their original order. These removals concern this
item's route only: no dependency module is withdrawn, and no claim is made that another
consumer or the targets' full import closure no longer needs it.

## Where the brief, the DAG or earlier work was wrong

The planned general-cocycle specialization was unnecessary. The existing exact-functor
square-pasting theorem and mate-composition API give a direct proof after checking the
normalization of the specified associator. No statement was false or changed, and no
extra geometric or coefficient hypothesis was added.

The launcher began trying a local build mirror during the session; it lacked required
Lean artifacts. Subsequent checks use the launcher's supported `LCOMPILE_NO_LOCAL=1`
setting to respect the server-only compilation brief. Launcher scripts were not changed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
