## What changed

Restored the assigned quarantined module and proved
`DerivedCategory.integral_bounded_kunneth_exact` from the stated bounded tensor-Tor
spectral sequence. The original public signatures, definitions, attributes and public
imports are preserved. Removed the redundant private imports of spectral-sequence basics,
filtration and adjunction limits; their public interfaces are supplied by retained imports.
All added helpers are private and proved.

The proof constructs a two-term flat resolution from a projective presentation to
establish higher integral Tor vanishing, proves two-column degeneration with natural
stationary-page comparisons, identifies the finite filtration's endpoints, and transports
the resulting short exact sequence to the stated tensor and Tor direct sums. Naturality
uses the maximum of the two stabilization thresholds, so the eventual graded comparisons
are compared on the same page. No splitting or finite-generation hypothesis is used.

The existing node records the implemented projective-presentation version of its five
steps. The change record
`coord/changes/integral-bounded-kunneth-proof-scoping.md` documents proof options and
the additional universe used only by private categorical helpers. No consumer adaptation
is required.

## Proved and sorry left

Closed: `DerivedCategory.integral_bounded_kunneth_exact` (the original single hole).
Added holes: none. Remaining local holes: none. Split off: none.

The candidate contains zero `sorry` tokens. Static comparison against the current
quarantine archive confirms all five original public abbreviation/definition bodies,
the theorem signature and public imports are verbatim. There are no lines over 100
characters. The retained node differs from the live node only in `proof` and
`proof_origin`, and all six dependencies retain their declarations.

The full actual module compiled against the real bounded spectral-sequence dependency
in 40.3 seconds. The only warning requested a comment explaining the scoped heartbeat
allowance; that comment is now present. The three redundant private imports were then
removed. Final compilation and axiom checks run through `deliver3.py`.

The initial delivery request and several profiling requests met busy-server responses;
they were retried. The retained candidate needed no mathematical change after the compile
service began supplying the committed dependencies absent from the published build.
No dependency substitute or scratch placeholder is part of the delivery.

## No longer needed

Removed private imports:

- `Mathlib.Algebra.Homology.SpectralSequence.Basic` (publicly supplied by the spectral-sequence
  dependency).
- `WeilConjectures.CategoryTheory.Abelian.Filtration` (publicly supplied by the same dependency).
- `Mathlib.CategoryTheory.Adjunction.Limits` (publicly supplied through the retained monoidal
  closed imports).

All six planned proof dependencies remain used: the bounded spectral sequence,
PID torsion-free flatness, flat-resolution Tor comparison, spectral-sequence structure,
Tor functors and decreasing filtration. No module or node is withdrawn. All original
public imports are preserved. No node or module becomes unnecessary from these redundant
import removals.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The module's absence from `lean/` was the
recorded quarantine, not withdrawal. Its archive is preserved and its existing Lean
attachment and parent dependencies remain intact. The planned free presentation is
replaced by the degree-zero projective presentation of Mathlib's projective resolution;
projectivity supplies flatness and torsion-freeness, and the same two-term argument applies.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
