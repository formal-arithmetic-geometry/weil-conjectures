## What changed

Proved `Module.exists_maximal_nowhereDense_support_quotient` in
`Sheaf.RingTheory.RemoveEmbeddedPrimes`, with its statement unchanged. Constructed K
as the intersection of localization kernels at the minimal support primes, the
kernel characterization in Stacks Tag 02M6's maximality argument. Proved the
nowhere-density/generic-point bridge and associated-prime/support comparisons as
private helpers. Updated the theorem's proof description and the existing node's
proof route to match the Lean proof.

Added private proof imports of Mathlib's `Spectrum.Prime.Noetherian`,
`Spectrum.Prime.Module`, and `Ideal.AssociatedPrime.Localization`. The four existing
public imports remain necessary for the public statement. No interface or consumer
adaptations are required.

The complete module compiles without warnings through lcompile.py. The theorem's
axioms are checked with `#print axioms`; only propext, Classical.choice and Quot.sound
are used. All declarations are proved directly from Mathlib. The universal argument
includes the zero module and zero ring, empty minimal-prime sets, f=0, and f=1:
no nontriviality or nonempty index hypothesis is added.

## Proved and sorry left

Closed 1 existing hole:
`Module.exists_maximal_nowhereDense_support_quotient`
(node `lem-sc-hilbert-embedded-points-affine-removal`).

Added 0 holes. There are 0 sorries left in the module or elsewhere in this delivery.
All seven private helper theorems are proved. No statements are split off.

## No longer needed

Removed `lem-weil-pbc-noetherian-associated-primes-finite` from this node's
proof dependencies: the kernel construction does not enumerate associated primes
or use their finiteness. This was a Mathlib leaf, with no separate Sheaf module to
withdraw. No existing import was removed and no library module is withdrawn.
The remaining four declared dependencies are used through their Mathlib records.
No other node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The previous route first constructed K using the
union of embedded-prime zero loci. The equivalent kernel construction exposes
maximality directly and avoids that enumeration; the node now records this route.
The blueprint unit's statement and route are preserved. No new nodes, definitions,
source-library changes, or forced adaptations are needed.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
