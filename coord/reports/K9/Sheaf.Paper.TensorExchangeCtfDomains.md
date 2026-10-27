## What changed

Filled all three proof bodies in Sheaf.Paper.TensorExchangeCtfDomains, preserving each
statement verbatim. The finite Hom proof chooses bounded constructible etale origins,
reflects the two exact Tor intervals, applies finiteCoefficient_derivedHom_ctf_etale,
uses the evaluation-defined site comparison, and transports the resulting interval and
constructibility through intrinsic coefficient realization and the input isomorphisms.
No separatedness of the structure morphism or site-perfectness is added.

The completed Hom proof applies integralHomReduction, converts legacy completeness
using sfDerivedComplete_iff_legacy, and applies the finite theorem to every reduction.
The tensor-unit K-flat test supplies the uniform cohomological support. The integral
direct-image proof applies sfCompleteDirectImage_reduction and the finite-coefficient
direct-image theorem levelwise, transports through the actual projection adjuncts,
and obtains both integral domains and their equality from integral_residue_tor.

Added two new modules containing the precise remaining transport/coherence obligations.
Added private proved helpers for Tor/support and constructibility transport and for
invertibility of the coefficient prime on the base schemes. All added proof imports
are private. No source-library module or target is edited.

Validation: all three delivered modules compiled successfully on the server through
lcompile.py (result 35dc5f869171e908aa270552, exit code 0). All three original
signatures compared verbatim to the current source; all new node dependencies exist;
all delivered Lean lines have at most 100 characters. Delivery preflight performs the
compiler axiom and direct-hole probes. Small cases reviewed: dimension zero gives
[c-b,e-a] and [a,b]; n=0 is only an integral reduction index and means exponent 1;
finite n is positive; zero inputs, zero rings in the transport lemma, empty schemes,
and nonseparated structure morphisms introduce no additional hypotheses.

## Proved and sorry left

Closed the three original direct holes:

- WeilConjectures.tensorExchange_finiteHom_domains
- WeilConjectures.tensorExchange_integralHom_domains
- WeilConjectures.tensorExchange_integralDirectImage_domains

No sorry remains in the item module. Added two whole-proof public theorem holes:

- AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport in
  Sheaf.Paper.IntrinsicSiteHomTransport, node lem-sf-intrinsic-site-hom-transport.
- WeilConjectures.sfDirectImageReductionComparison_transition in
  Sheaf.Paper.SfDirectImageReductionTransitions, node
  lem-sf-direct-image-reduction-transitions.

This is a decomposition of three direct holes into two strictly smaller general
coefficient-presentation/coherence obligations, with complete combining proofs.
The source/theorem dependencies used by the combining proofs may themselves rest on
sorry; this report does not claim axiom-free completion of their transitive closure.
Direct hole count: 3 closed, 2 added, net 1 closed across the delivered modules.

## No longer needed

None. Every original proof dependency remains used. The finite Hom argument retains
finiteRing_constructibleDerived_origin, both ComparisonTorAmplitude directions,
finiteCoefficient_derivedHom_ctf_etale and the canonical Hom site comparison. The
integral arguments retain the normalized Hom reduction, residue-Tor equality,
complete-direct-image reduction, finite direct-image bound, and recorded definitions.
No module, node, unit step, public import, or maintainer tool-use approval is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The plan correctly supplies the geometric bounds. Its coefficient-presentation
identification and final adjacent transition square need explicit bridges between
the actual recorded constructions: a fixed-scalar Hom is not definitionally the
intrinsic Hom-complex localization, and an arbitrary reduction isomorphism alone
does not establish a square between specified maps. Those steps are now separate
named obligations with complete natural-language proofs and exact Lean signatures.
No mathematical statement is disputed or weakened. The latest blueprint moved the
parent to sec-six-functors/sk-thm-sf-package; sources were read at that current path.

## New nodes

lem-sf-intrinsic-site-hom-transport identifies ambient internal Homs under the existing
exact constant-scalar realization equivalence, without finiteness or constructibility
conditions on the complexes. This is only the coefficient-presentation portion of
Step 2 of the finite Hom proof, with no bounds or geometric argument repackaged.

lem-sf-direct-image-reduction-transitions proves just the adjacent quotient square for
the specified projection adjuncts, for arbitrary schemes and complexes, without
asserting completeness, constructibility, bounds, or invertibility. Its proof isolates
the Roos cone relation and normalization of scalar adjunctions and quotient transitions.

Change record: coord/changes/K9-tensor-exchange-transport-lemmas.md.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
