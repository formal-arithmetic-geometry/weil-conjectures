## What changed

Filled four of the five named theorem proofs in
`lean/Sheaf/Paper/ExceptionalFiniteRealization.lean` without changing their signatures or the
constructions they justify. Added private proof imports for sheaf composition, inverse mates,
the mate transpose equation, and Cartesian sheaf products. Added proved private helpers for
restriction along a ring-sheaf isomorphism and the constant-section scalar equations.

The ordinary direct comparison is built from `A.rightUnderlying` itself: its adjunction
normalization and the `moduleAdd`/`moduleSMul` fields prove linearity. Its inverse comparison is
the inverse mate. The derived comparison remains unproved. The item node records the four
completed steps and retains the final derived step.

## Proved and sorry left

Four original holes closed; the complete module compiled through `lcompile.py` in 54.7 seconds:

- `WeilConjectures.integralExceptionalEtaleForget`.
- `WeilConjectures.integralExceptionalEtaleRealization_properties`.
- `WeilConjectures.integralExceptionalEtaleRight_existsUnique`.
- `WeilConjectures.integralExceptionalEtaleInverse_existsUnique`.

One original hole remains: `WeilConjectures.integralExceptionalEtaleDerivedRight_existsUnique`.

No holes were added or split off. The four completed proofs and the remaining theorem belong to
`def-pur-adic-etale-realization`.

## No longer needed

None. The node had no prescribed proof dependencies to prune. All original public imports remain
needed by its statements or constructions. The unit route is preserved. The new proof uses
existing proved generic scalar-restriction and mate APIs. The unused private proof import
`Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares` was removed when deferring the derived
proof; its nodes are not new proof dependencies of this partial delivery.

## Where the brief, the DAG or earlier work was wrong

The node originally had an empty proof plan. Its proof and proof dependencies now describe the
actual argument. No mathematical statement or definition was changed. The quotient equivalence is locally
irreducible while checking the comparison proofs, preventing needless reduction of its
explicit quotient construction; this does not change its exported attributes or body.

The derived proof candidate uses the existing generic `rightDerivedSquare` and
`cochainRightUnit_universal` helpers. Its normalization requires explicit identity
simplification and avoiding unfolding the concrete realization during Kan-extension comparison.
This combined proof exceeded the fixed compile limit, so the original derived theorem is left
untouched.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
