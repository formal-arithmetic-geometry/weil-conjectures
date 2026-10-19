## What changed

Proved `IsUniversallyCatenary.of_local_depth_eq_dimension` in
`Sheaf.RingTheory.CohenMacaulayRingUniversallyCatenary`, with its signature,
visibility, public imports and existing docstrings unchanged. Added the proof-only
import `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and proved five private
helpers for maximal chains, full-height prefixes, concatenation, the height
difference formula, and transport along a surjection.

The proof follows Stacks Algebra, Tag 00NM (algebra.tex, lemma-CM-ring-catenary),
using the declared polynomial Cohen–Macaulay theorem (00ND), and the declared
maximal-chain theorem (00N9). Mathlib's full-height prefix realizes the lower
height without a second use of 00N9. A finite polynomial presentation and the
quotient spectrum order isomorphism supply both catenarity conditions. Updated
the existing node's proof, proof_deps and proof_origin accordingly; no unit route
or statement changed.

Searches via msearch leanfinder, loogle and grep found no matching theorem.
Read the already proved field-base argument in
`WeilConjectures.RingTheory.PolynomialRingMaximalChainHeightDifference` and reused
its elementary order-theoretic argument, replacing regular local depth by the
Cohen–Macaulay equality. The field-base theorem itself is not imported.

Server compilation through lcompile succeeded without diagnostics. The proof
covers length-zero chains, equal endpoints, zero variables and the zero ring;
none of the helpers assumes a domain or a nontrivial base ring.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsUniversallyCatenary.of_local_depth_eq_dimension`
(node `lem-trf-cm-ring-universally-catenary`).

Added 0 holes. No sorry remains in the delivered Lean module. All five private
helpers are proved. This proves the item from its existing declared dependencies;
`MvPolynomial.isNoetherianRing_and_local_depth_eq_dimension` remains an existing
upstream obligation, and the maximal-chain theorem's own proof dependencies are
unchanged. Neither dependency is restated or altered in this delivery.

## No longer needed

No original import was removed: both original proof imports are used.

Pruned the proof dependency `lem-weil-pbc-noetherian-local-finite-krull-dimension`:
Mathlib's finite height for every prime of a Noetherian ring directly bounds
chains and supplies the natural number dimension of the upper localization.
Its generic Mathlib fact remains valid, but this proof does not use the
Noetherian-local finite-dimension instance.

The second application of 00N9 to the lower localization is unnecessary because
`Ideal.exists_ltSeries_length_eq_height` directly supplies a full-height prefix.
The maximal-chain node and its module remain needed for the upper localization.
No other node or module is pruned. No new modules were introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit route was wrong. The DAG planned a redundant
second maximal-chain argument and a separate local finite-dimension input;
the updated route uses Mathlib's finite prime heights and full-height prefix.

An initial single-file server compile found a published dependency importing
the retired `Sheaf.RingTheory.Depth`, conflicting with
`WeilConjectures.RingTheory.Depth`. Compiling the current, byte-identical source
of `PolynomialAlgebraCohenMacaulay` in the sandbox resolved that cache mismatch.
That unchanged dependency is excluded from the delivery. No library source,
launcher script or definition was modified to work around the conflict.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
