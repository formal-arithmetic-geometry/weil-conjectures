## What changed

Proved `AlgebraicGeometry.ProEtale.AffineZeroPurity.unit_finiteTor` in
`Sheaf.Paper.AffineSpaceZeroSectionPurity` from the existing constructibility and
Tor-amplitude APIs. A proved private helper treats an arbitrary coefficient ring.
The constant-sheaf monoidal unit isomorphism transports constructibility and
flatness; its degree-zero complex then has Tor amplitude [0,0].

Local irreducibility keeps large imported tensor, inverse-image, shifted-line and
constant-sheaf constructions from unfolding in later comparisons. Completed local
comparison objects are likewise kept locally irreducible before their later uses.
The local section ends before the exact base-change construction.
No definition body, signature, import or exported attribute changes.
The complete module compiled in 28.9 seconds with profiling enabled; the profiler
option was removed for delivery.

## Proved and sorry left

Closed 1 of the 6 original holes on the current source:
`AlgebraicGeometry.ProEtale.AffineZeroPurity.unit_finiteTor`.
No holes added or split off. Five original named theorem holes remain, all attached
to `cor-pur-affine-space-zero-section-purity`:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.targetSourceRaw_left`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.normalizationRaw_left`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_untwisted`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_baseChange`

The six supporting proofs landed by F4 during this session are retained and are
not counted as this delivery's closures.

## No longer needed

No import removed, no node withdrawn and no module deleted. All five planned proof
dependencies remain needed for the unfinished main statements; this partial proof
does not replace that route.

## Where the brief, the DAG or earlier work was wrong

The stated product-recursion and tower-normalization modules import this module
for its construction API. They cannot be imported here without a cycle. The next
assembly needs to move the shared constructions into a lower module, re-export
that API here and adjust the dependency modules. This delivery adds no replacement
hole or duplicated version of those lemmas.

The latest blueprint distinguishes the positive Cartier-Chern product, which
integrates to one, from the positive localization-boundary product, which integrates
to (-1)^c. The current `supportedClass` uses the Cartier maps, so its normalization
statement is retained. No assertion identifying it with the oppositely signed
orientation is added. The current node prose predates that explicit sign distinction.

The source changed during this session when the F4 delivery landed. This packet is
rebased onto that delivery, preserving its six completed supporting proofs and
its removal of unused proof imports. Endpoint proofs and a refactor of the raw
Sigma constructors were explored but exceeded the fixed file compilation limit;
they are not part of this packet. The delivered finite-Tor argument is stated first
at an arbitrary coefficient ring to avoid the expensive scalar conversion.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
