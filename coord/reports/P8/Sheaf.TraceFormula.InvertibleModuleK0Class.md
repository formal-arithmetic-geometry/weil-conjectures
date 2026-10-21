## What changed

Proved `Module.FiniteProjectiveK0.class_of_finite_free_resolution` in
`Sheaf.TraceFormula.InvertibleModuleK0Class`, preserving its full statement.
Private proved helpers establish invariance under linear equivalence, additivity
for products, and the class of a finite free module directly from the existing
K₀ presentation. The main proof follows Stacks Tag 0AFY and the node's four
steps: split the first surjection by projectivity, prove its kernel is finite
projective, apply induction to the remaining resolution, and subtract its class.
The length-zero case uses the endpoint bijection explicitly.

Added proof-only Mathlib imports for finite sums, finite-coordinate linear
isomorphisms, finite-basis finiteness, and finiteness of products. No public
interface, definition, source-library module, or DAG route changed.

Repaired the return for delivery head `33bd9a671`: removed the unnecessary
`set_option warn.sorry false`. The ledger interpreted the option name as an
unattributed hole after the new imports shifted its source position. The
source ledger now reports five named proved declarations, zero hole markers,
zero scanner warnings, and no supplemental gate failures.
The repaired module compiled on the project server in 6.2 seconds, with no
diagnostics; its statement comparison reports no changed signatures.
Preflight requires a change record for the file-level warning-option removal:
`coord/changes/p8-invertible-module-k0-warning-option.md`. It records the exact
old/new option block and verifies that no consumer adaptation is needed.

## Proved and sorry left

Closed 1 of 1 holes:
`Module.FiniteProjectiveK0.class_of_finite_free_resolution`
(node `lem-trf-invertible-module-k0-class`). Added 0 holes; split off 0.
No `sorry` remains in any declaration of this delivery.

## No longer needed

None. The original public import `Sheaf.RingTheory.FiniteProjectiveK0` remains
necessary. All five declared proof dependencies are used: the K₀ presentation,
finite generation, projectivity, finite free bases, and exactness. No nodes or
modules are withdrawn, and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The K₀ module provided the construction
but no isomorphism/additivity API; the required facts are proved privately here.
Mathlib's `Function.Exact.splitSurjectiveEquiv` supplies the splitting directly.
The Mathlib searches found no existing K₀ Euler-class theorem.
The returned unattributed hole was the warning option, rather than a missing
proof. Removing that option repairs the packet without changing a statement
or definition.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
