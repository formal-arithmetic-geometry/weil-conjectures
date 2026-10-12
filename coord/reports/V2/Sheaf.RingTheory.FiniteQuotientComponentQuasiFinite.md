## What changed

Proved `Algebra.isQuasiFiniteAtPrime_of_finite_quotient_component` in
`Sheaf.RingTheory.FiniteQuotientComponentQuasiFinite`, preserving its signature and all
public imports. Added the proof-only import `Mathlib.RingTheory.QuasiFinite.Basic`.
Updated the node `lem-weil-pbc-integral-closure-finite-fibre-quasi-finite` to record the
implemented route: the finite component has discrete fibres; its image is relatively
open in the quotient locus; compatibility identifies its fibre with an open part of
the original fibre; the fibre homeomorphism transfers the isolated point.

The proof uses only existing Mathlib results and elementary ideal/topological arguments.
LeanFinder and Loogle searches found quasi-finite/discrete-fibre results, but no exact
finite quotient component theorem. Repository and Mathlib source searches confirmed the
spectrum embeddings, product homeomorphism, and discrete subset lemmas used here.

## Proved and sorry left

Closed the sole original hole:
`Algebra.isQuasiFiniteAtPrime_of_finite_quotient_component`
(node `lem-weil-pbc-integral-closure-finite-fibre-quasi-finite`).
No holes remain and no holes were added. This is a proof, not a decomposition.
Single-file compilation succeeds with no warnings; the delivery dry run checks axioms.
The zero component and I=top cases are vacuous because the proof starts from an actual
prime of C₁; no nonzero-ring assumptions or choices of algebraic witnesses were added.

## No longer needed

No original imports were removed. No Sheaf proof-dependency modules need to be imported.
The explicit construction of F/(1-e)F, its finite spanning family, and the removal of
other finitely many closed fibre points are unnecessary: Mathlib's discrete-fibre and
discrete-subset lemmas supply their combined consequence.
`lem-weil-pbc-spec-clopen-idempotent` is no longer a proof dependency: openness comes
from `PrimeSpectrum.primeSpectrumProdHomeo` and `isOpenMap_inl`.
`def-weil-pbc-localization-at-prime` and `def-weil-affine-spectrum` are no longer separate
proof dependencies; their interfaces remain available through the predicate's public
imports. The fibre-prime correspondence, quasi-finiteness definition, and finite-fibre
discreteness remain used. The quotient-spectrum embedding node is now explicitly used.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface problem found. The original seven-step fibre-ring plan
is valid but longer than necessary. The mathematical finiteness argument can be used
through Mathlib's `Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton` directly on
Spec(C₁) over Spec(A/I), and then transferred through the spectrum embedding.
The quotient-spectrum node's match writes `PrimeSpectrum.range_comap_of_surjective`,
but the actual declaration in this Mathlib is the unnamespaced
`range_comap_of_surjective`; the proof uses its actual name.

## Second reading by V2

1. Compared the sole delivered module with the repository using `diff`. The existing
   theorem signature is byte-for-byte identical (also checked by exact string comparison).
   No definition, visibility, or public import changed; the only new import is proof-only.
   No change record or forced adaptation is needed. Verdict: pass.
2. Compiled the module with `lcompile.py`: no errors or warnings. Independently compiled
   a scratch copy with `#print axioms
   Algebra.isQuasiFiniteAtPrime_of_finite_quotient_component`; the result is exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the proof
   throughout: no sorry, forbidden declaration, or data chosen from an unproved theorem.
   Verdict: a complete proof of the unchanged statement.
3. No statements were split off and no declarations or nodes were added. Checked the
   degenerate cases: a zero first component has no primes, and I=top forces that case;
   a zero second component causes no problem for the product-spectrum embedding.
   The compatibility hypothesis is used in both directions of the fibre identification.
   Verdict: no new statement or hidden hypothesis to review.
4. Read Mathlib's finite-module quasi-finite instance and
   `Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton`, and searched the local
   ring-theory library for quotient/component quasi-finiteness results. No direct shorter
   theorem was found. The original public imports support the quotient/product statement;
   the added private import supplies fibre discreteness. All three removed old DAG
   dependencies are named under No longer needed. Read `dag/units/sk-thm-p1.json`:
   neither this auxiliary node nor the removed dependencies realize a unit statement or
   step, and no unit route is bypassed. No modules were pruned. Verdict: pass.
5. Compared the delivered node with its original: only `proof`, `proof_deps`, and
   `proof_origin` changed. The four recorded steps follow the embedding, discrete fibre,
   fibre identification, and fibre-homeomorphism arguments in Lean; proof_deps is exactly
   the union of their uses, with the Mathlib leaf supplying finite-fibre discreteness.
   No new-node fields are required. Verdict: pass.

Changed only the theorem's proof docstring to describe the implemented four-step
argument instead of the superseded seven-step plan. The proof term, signature, imports,
node, and hole counts needed no repair: one hole closed, zero added.
