## What changed

Filled both proofs in `Sheaf.RingTheory.TransversePrimeIdealParameters`, preserving their
signatures and all public imports. Added the proved private helper
`RingTheory.parameter_subset_quotient`, which orders a chosen subset of parameter indices
before its complement and applies the existing parameter-quotient theorem.

For `RingTheory.exists_parameters_of_transverse_primes`, the individual quotient-kernel
and dimension theorems first show that every prime is principal. Applying the same theorems
to the total ideal identifies its kernel parameter count with `r`. Replacing those first
`r` generators by the chosen principal generators preserves the generated ideal and the
length of the full parameter list, giving the required simultaneous system.

For `RingTheory.parameter_product_ideal_properties`, singleton quotients give prime
coordinate ideals. The dimension drops for singleton and two-element subsets show that
coordinates are nonzero and their ideals are incomparable. A finite divisibility induction
identifies the product ideal with the intersection. Radicality and the precise minimal
primes follow from primality and incomparability. The subset helper proves all stratum
clauses, and the empty-product clause is proved explicitly.

Updated the item's DAG proof and proof dependencies to this implemented route. No other
existing modules or nodes change. No definitions, attributes or public interfaces change.

## Proved and sorry left

Original holes: 2. Closed:

- `RingTheory.exists_parameters_of_transverse_primes`.
- `RingTheory.parameter_product_ideal_properties`.

Both realize `lem-sfb-transverse-prime-ideal-parameters`. Added holes: 0. Remaining holes
in the delivered module: 0. No split-off statements or modules.

## No longer needed

The direct proof import `Mathlib.RingTheory.Regular.RegularSequence` and the unused public
import `Sheaf.AlgebraicGeometry.IsRegularScheme` are removed: the proof uses the quotient conclusions of the already imported parameter theorem,
without using regular-sequence assertions. Accordingly
`def-weil-pbc-regular-sequence` is removed from the item's proof dependencies.
`def-weil-regular-scheme` is not used by the Lean statement or proof and is pruned from the
proof route; the theorem signature uses `IsRegularLocalRing` directly.

The separate lift-and-generate argument for the maximal ideal of the total quotient is
unnecessary, because the existing quotient-kernel theorem supplies the complementary
parameters. The regular-sequence argument for coordinate nonmembership is replaced by
comparing the one-coordinate and two-coordinate quotient dimensions. All three substantive
algebra inputs remain: the quotient-kernel theorem, the parameter-quotient theorem, and the
regular-local-domain theorem. No source-library declarations or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statements or unusable dependencies were found. The first theorem's distinctness
hypothesis is unnecessary for this proof, but is preserved verbatim. The original route is
valid; its two auxiliary arguments can be shortened using the already stated theorems.
The empty family, dimension zero, singleton subsets, and the full parameter subset are
included in the list, finite-set and arithmetic proofs.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
