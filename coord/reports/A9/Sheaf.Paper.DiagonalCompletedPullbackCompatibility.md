## What changed

Replaced the sole sorry in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_completedPullback`
by an assembly proof. The signature and the two existing public imports are unchanged.
The proof transports the realized class using the two `Reference.delta` equations,
proves that both product projection squares are Cartesian by pullback pasting, and
applies one projective-line trace result three times. A private proved cancellation
lemma solves each `CompletedTraceCompatibility` equation for the realized trace,
then identifies it with the given family trace. A private trace-transport lemma
shares this cancellation across the three uses to keep elaboration within the
heartbeat budget. The full canonical derived-unit
normalizations are passed to each trace application.

Added two new modules, containing the narrower class and trace obligations and one
proved isomorphism lemma. These are distinct mathematical parts of paragraph (3),
not a copy of the complete compatibility statement. The class assertion has no
trace data, no coefficient Family, and only the surface localization choices.
The trace assertion has no diagonal arrow, no Family, and works for one arbitrary
Cartesian square of projective-line models; it is reused for q, p1 and p2.

Validation: `lcompile.py --all` compiled both new modules. After factoring the
trace transport and making the product-map unfoldings explicit, the final item
compiled successfully with `lcompile.py` in 25.1 seconds. Static checks confirmed
the unchanged original signature, matching new Lean/node statements, and the
two named theorem holes listed below. No library build was run by this worker.

## Proved and sorry left

This is a decomposition, not a net proof of the compatibility obligation.

Closed the original textual hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_completedPullback`
(node `lem-diagonal-completed-pullback-compatibility`). Its assembly proof has no sorry.

Added two holes, each the complete proof of a public named theorem:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCompletedClass_pullback`
  in `Sheaf.Paper.DiagonalCompletedClassPullback`, node
  `lem-diagonal-completed-class-pullback`.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCompletedTrace_pullback`
  in `Sheaf.Paper.DiagonalCompletedTracePullback`, node
  `lem-diagonal-completed-trace-pullback`.

The same trace module proves
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRealization_shiftedLine_isIso`.
The item proves its private trace cancellation and two Cartesian-square helpers.
There are no holes in definitions. Textual accounting: one old hole closed, two
holes added, net minus one. No claim of a sorry-free axiom closure is made.

## No longer needed

No existing public or proof import was removed, and no module is withdrawn or
claimed globally pruned. The item's nine former direct proof dependencies are
now delegated to the two strictly narrower nodes, rather than bypassed:
`det-pe-topos-functoriality-inverse-image`, `det-prop-diagonal-tower-limit`,
`det-prop-diagonal-tower-system`, `det-prop-diagonal-tower-trace`,
`lem-weil-pbc-proetale-abelian-closed-support`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `sk-lem-geo-cartier`,
`sk-lem-geo-p1-cohomology`, and `sk-prop-sfb-cartesian-coefficients`.
Their union remains the proof plan below the new nodes. The assembly itself needs
only the two new proof imports and the existing publicly exposed interfaces.
The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The finite Cartier base-change theorem
and the finite P1 decomposition do not themselves state the normalized
whole-system inverse-image/derived-limit square. In particular, finite reductions
cannot detect an arbitrary derived morphism. Both new nodes retain the missing
whole-system steps explicitly, with their source and proof in words.

The item had a quarantine entry referring to a false trace-tail import. Its
preserved archive was read before copying. During this session the live module
and its dependencies became available again; the starting archived item compiled.
No archive, Lean attachment, or dependency was deleted. This proof neither imports
nor invokes the false-tail lemma directly.

Edge checks: for an identity base change the equations express independence of
normalized presentations; for an empty scheme the endpoint and morphism equations
are unique. For a general Cartesian trace square, changing a projective-line
model can add a base class to its hyperplane class; that lies in the complementary
summand and does not change the trace projection. The new trace lemma retains
Noetherian and invertibility hypotheses and the full universal units, rather than
assuming an arbitrary mate is invertible or an arbitrary trace is canonical.

## New nodes

`lem-diagonal-completed-class-pullback` records just the source and completed
class square, without traces or scalar extensions. Its proof follows the positive
Cartier roof, simultaneous Kummer reduction, normalized limit naturality and
source/root realization normalizations in paragraph (3) of the current blueprint.

`lem-diagonal-completed-trace-pullback` records one realized projective-line trace
square and invertibility of its specified mate. Its proof follows the entire
unit/Chern splitting through the same limit comparison, then inverts and projects.
It also attaches the proved shifted-line isomorphism lemma. Both nodes include
LeanSearch, LeanFinder/Loogle and Mathlib/local grep search results. No matching
completed compatibility theorem was found. No change record is needed: existing
signatures, definitions, visibility and public imports are preserved.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
