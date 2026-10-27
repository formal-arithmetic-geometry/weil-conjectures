## What changed

Replaced the hole in ordinaryAmbientProperOpenLaws with a complete assembly of all twelve
Laws fields. The source-library derived pullback coherence theorems give pullback associativity
and units directly. Private generic conjugation calculations give direct-image and open-extension
associativity and units. Explicit applications of mateEquiv_hcomp, mateEquiv_vcomp, and their
conjugation/whiskering formulas turn the two alpha-pasting equations into the two gamma-pasting
equations. The generic identity-mate calculations give the two gamma identity equations.

The remaining exact-localization glue is stated in two new modules:
OrdinaryAmbientAlphaPasting contains only the two alpha-pasting equations;
OrdinaryAmbientAlphaUnits contains only the two alpha identity-square equations. Their docstrings
and nodes explain the proof from the existing underived pasting and exact-comparison declarations.
Local irreducibility keeps the concrete ordinary record folded during the new statements and
the final assembly; this resolves elaboration recursion without changing any shared definition.
All three modules compiled together successfully. The item signature, all existing public
declarations and public imports are unchanged.

## Proved and sorry left

Closed the original syntactic hole in
AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientProperOpenLaws
(node lem-sf-ordinary-ambient-proper-open-laws).

Added two holes, each the entire proof of a named public theorem:

- AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientAlphaPasting
  (node lem-sf-ordinary-ambient-alpha-pasting).
- AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientAlphaUnits
  (node lem-sf-ordinary-ambient-alpha-units).

This is a decomposition: 1 original hole closed and 2 strictly smaller holes added, for a
syntactic net of -1. It does not establish a sorry-free proof of the original theorem. The six
compositor laws and all four mate equations are proved in the item; the four non-mate geometric
equations are what remains. No hole is inside a definition or a private theorem.

## No longer needed

Removed the item's proof imports of AmbientUnderivedClopenPasting and
AmbientAdjunctionCompositorNormalization. The former remains a planned proof dependency of the
two new localization statements; it is not globally pruned. The broad normalization theorem is
not needed for the six compositor laws: these follow from the native source-library pullback
coherence and the generic adjunction API. The normalization module may remain transitively
imported by existing dependencies, so no global module pruning is claimed.

The original direct proof dependency lem-sf-ambient-adjunction-compositor-normalization is
replaced by the native coherence argument. The original underived and exact-clopen proof
dependencies now belong to the two smaller localization steps. No UNIT statement or proof step
is bypassed; this item's unit has no realized statement or steps.

## Where the brief, the DAG or earlier work was wrong

The item and some dependencies were initially absent from lean/ and present at their quarantine
paths. I read their rework rows and restored only the assigned source in the sandbox. During the
session the shared source tree was refreshed and those paths were restored; the earlier suspected
source-availability issue is resolved. The archive, original statement and node attachment were
preserved. A preliminary delivery attempt was interrupted before any push after that refresh;
it carried an incomplete proof and is superseded by this packet.

The original plan's general compositor-normalization theorem is more than this argument needs.
The existing native derived pullback API already contains its associativity and unit laws. The
remaining difficulty is the exact-localization comparison glue, rather than the generic mate
calculus. The new statements preserve all commutativity, openness, quasi-compactness, properness
and coefficient assumptions. Identity and empty-open cases are included; no Cartesian,
boundedness or separated-structure-map hypothesis is added.

Delivery is blocked by the launcher warning gate, not Lean errors or the compile-time limit.
Both completed delivery attempts compile all three packet files, then replay the same cached
SfP1ChartExchange diagnostics from dependency revision c0c6c1dbd53a01ace3cacf8b04fe35c4221e2554
(unused simp arguments ordinaryFinitePullback, ordinaryFiniteLine and ordinaryFiniteDegreeZero
at lines 565--566). The refreshed shared source already removes those exact arguments.
The required public AmbientProperOpenCalculus import brings this dependency transitively.
The retry still replays the stale cached diagnostics and exits COMPILES WITH WARNINGS (local),
nothing pushed. No launcher, cache, unrelated module or public import was edited to bypass it.

## New nodes

lem-sf-ordinary-ambient-alpha-pasting records only the vertical and horizontal alpha-pasting
component equations. Its proof localizes the existing ordinary underived equations, identifies
properOpenAlpha through the exact-clopen comparison, and identifies both kinds of compositors.

lem-sf-ordinary-ambient-alpha-units records only the two alpha identity-square component
equations. Its proof localizes the existing underived identity words and uses the prescribed
pullback identity and unit-normalized open-adjoint identity comparisons.

Both belong to sec-six-functors / sk-rem-sf-pf-done and have one new statement module each.
No existing interface was changed, so no change record or consumer adaptation is needed.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
