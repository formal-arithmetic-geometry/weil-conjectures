## What changed

Proved `AlgebraicGeometry.Etale.etaleCompactScalarComposition` from the existing proper/open comparison declarations. The proof normalizes the open coefficient comparison, proves the proper-refinement square and transfers it through a common refinement. It pastes the existing proper/open coefficient-mate square with the proper and open scalar composition identities in the compactification tower, and transports the result to the chosen compactifications.

The bounded-below checks are explicit: exact open extension preserves the input bound; proper direct image preserves bounded-below objects; the compact scalar isomorphism transfers the second required bound. No assertion that arbitrary scalar extension preserves bounded-below objects is used.

All existing declaration signatures, definitions and public imports are preserved. Added helpers are proved and private. No new modules, statements with holes, or definition repairs are proposed.

## Proved and sorry left

Original holes: 3. Closed: 1, `AlgebraicGeometry.Etale.etaleCompactScalarComposition`.
Added holes: 0. Split off: 0.

The following original holes remain unchanged:

- `AlgebraicGeometry.Etale.etaleCompactScalarCoherence` (node `lem-pur-etale-compact-scalar-coherence`).
- `AlgebraicGeometry.Etale.etaleCompactScalarUnit` (node `lem-pur-etale-compact-scalar-coherence`).

The full module compiled through lcompile.py after removal of unused exploratory imports (54.2 seconds, exit code 0). An earlier pair of diagnostic compilations failed before Lean started because the server device was full; the successful final compile followed those failures. The projection and unit experiments are retained outside the delivery Lean tree for continuation; they are not claimed as proved.

## No longer needed

None of the node dependencies is withdrawn: the proof follows the existing composition and refinement route, and the original projection and unit assertions remain open. All original public and private imports remain. Exploratory proof imports for derived tensor right exactness, monoidal conjugation, sheaf-compose monoidality and scalar-pullback existence were removed from the proposed module because this composition proof does not use them. No source-library declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or change of mathematical route. The original declarations are usable. The additional bounded-below hypotheses in the existing proper/open mate and refinement interfaces require the explicit preservation and isomorphism-transport checks included here. The transient remote disk-full failures are recorded above; the final module compile succeeded.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
