## What changed

Proved `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryOpen_mate` in the assigned module without changing its statement or any public definition. Added private proof imports of the varying-ring operations, strict-tower exact mate calculations, and the adopted exact-single coherence API. All additional constructions and lemmas are private and fully proved.

The argument identifies the recovered ordinary comparison with the already invertible ordinary inverse mate, proves the constant/single mate equation, then pastes the two squares and retains the exact realization equality transports. The item node records these four steps.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryOpen_mate` (node `lem-sp-varying-ring-ordinary-open-unit`), the sole original hole.

Holes added: none. Sorries left in the delivery: none. No split-off statements.

Validation: the complete proof compiled through `lcompile.py` in 27.2 seconds with profiling enabled. The final packet removes the profiling options and the unused simp arguments.

## No longer needed

None. No imports were removed and no nodes or modules were withdrawn. All four declared dependencies still serve the proof; the mate-pasting dependency is used through its Mathlib match. No cartesian square, clopen projector, proper/open pasting result, or the still-unproved ordinary comparison normalization theorem is used.

## Where the brief, the DAG or earlier work was wrong

The existing plan was mathematically sound. Its recovery step can be implemented more directly by localizing the already invertible ordinary inverse mate, identifying that localization with evalJInv, and recovering the resulting isomorphism through full faithfulness. This closes the previously split normalization obligation without further decomposition. The proof is uniform in the rings and includes the zero ring and empty open: all steps use categorical adjunction and exact-functor identities.

Computing the final component equations directly in the geometric categories was expensive for the kernel. Proving the same two paste formulas privately over abstract categories, then specializing them, makes the complete module compile within the limit without changing a shared definition or disabling transparency checks.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
