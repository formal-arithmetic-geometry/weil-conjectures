## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.RationalP1.second_trace_reordering` by an explicit
composition of the trace-free projection/exchange calculation and the scalar
trace square. The existing declaration signature and public imports are unchanged.
The sole added proof import is `Sheaf.Paper.RationalP1SecondScalarTrace`.

Added `RationalP1SecondPretrace` with explicit, constructed maps: the first
shifted-line comparison, scalar exchange, derived monoidal unit and tensor
comparisons, Koszul swap, conjugated tensor strength and projection-only part of
the counit. Two named structure definitions cache the canonical monoidal
pullback and native Koszul braiding without changing their data. None chooses data from a postponed existence assertion.
The sole-field proposition `SecondPretraceEquation` checks the literal equality
at a variable coefficient ring before specializing it, as the existing
`SecondTraceEquation` does for the final equation. This packages no additional
mathematical assumption. Its remaining
statement concerns only projection/exchange coherence, with no trace, Reference,
Family, counit normalization or localizing-closure hypothesis.

Added `RationalP1SecondScalarTrace`: invertibility and compatibility of the scalar
exchange with the two normalized traces. This has no arbitrary K, tensor action,
projection contraction or counit. Thus neither new statement is the item renamed
or with its hypotheses repackaged. Together they are the two distinct steps of
the original node, with the combining tensor argument now written in Lean.

Private helpers prove strength naturality, the monoidal right-unit law, evaluation
against any scalar map, naturality of the native tensor-shift comparison, transport
of evaluation through the tensor-shift isomorphism, and the literal factorization
of counitComponent. The final proof applies those lemmas, cancels the invertible
scalar exchange and rewrites the sole field of SecondTraceEquation.

Validation: `lcompile.py --all` accepted all three modules under its per-file
60-second acceptance limit. Its style diagnostics have been applied; the delivery
compile checks the final cleanup as well.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.RationalP1.second_trace_reordering` is removed.
This is a decomposition of one original hole, not a completed proof independent
of new obligations. Two holes are added, each the whole body `:= by sorry`:

- `AlgebraicGeometry.ProEtale.RationalP1.second_pretrace`, node
  `lem-sfb-rational-p1-second-pretrace`.
- `AlgebraicGeometry.ProEtale.RationalP1.second_scalar_trace`, node
  `lem-sfb-rational-p1-second-scalar-trace`.

There are zero holes in the item module and exactly two in the new modules.
All private categorical helpers and the combination proof are complete.
No definition contains a hole. The hole count increases by one (one removed, two added), giving net
closed-minus-added progress -1 before the ledger computes import-closure effects.

## No longer needed

No original import is removed; the three public imports are needed by the
unchanged signature. No existing module is withdrawn or claimed globally pruned.
The old direct proof dependencies for ringed exchange/tensor coherence,
module/ringed comparison and projection/tensor composition now belong to the
trace-free step, rather than being direct dependencies of the assembly. The scalar step uses the given Reference and Family normalizations. The
ringed coherence nodes remain needed, and are not global pruning claims.

The old direct dependency `det-prop-diagonal-tower-coefficients`
(`Sheaf.Paper.DiagonalTowerCoefficients`) is not needed in this route: existence of a coefficient family is not required when Family
and Reference are already arguments. The scalar step uses their fields directly.
This is a local dependency removal, not a claim that the coefficient theorem
is unused elsewhere in the library.

`det-thm-sf-pf-field-localizing` from
`Sheaf.Paper.RationalLocalizingProjectionFormula` is not needed to obtain the inverse
projection in the combination: the counit normalization already supplies hq, and the equation
supplies hb and hp. Its public localizing-closure type stays in the original
signature. No proof-dependency import is added merely to restate an assumption.

## Where the brief, the DAG or earlier work was wrong

The two prose steps in the original node are genuine separate tasks. The generic
ringed theorems do not immediately have the published internal-module arrows of
this item. In particular, their normalization transport and the even Tate-line
interchange are part of the trace-free statement, not consequences of endpoint
matching alone. The existing integral TraceBaseChangeSecond assumes the scalar
trace square, so using it would not prove that square. The general
`diagonalTower_coefficients_baseChange` takes completed reduction/limit data and
a second whole family, which are not supplied by this item's Reference.

A traversal of the dependency graph encounters a pre-existing cycle between
`lem-pc-ring-hom-extension-differential` and its `-adjacent` node (proof and
statement dependencies). Neither node is edited. A separate reachability check
confirms that no dependency path returns to any of this packet's three nodes.

No original statement is disputed or changed. Edge checks: K=0 makes both sides
of the trace-free identity zero; that step is independent of traces. In the scalar
step both finite rational coefficients and the closure are retained, and the
shifted line and unit have the common lower bound -2 used for bounded continuity.
The scalar exchange is invertible by its square with the unit/Chern splittings,
without invoking the general proper base change theorem. The degree-two Tate
interchange has sign (-1)^4=1. The inverse of beta is used
only with the supplied/proved IsIso witness. No integration or diagonal-class
identity is used, and the unit's prescribed second-triangle route is retained.

## New nodes

`lem-sfb-rational-p1-second-pretrace` records the trace-free part, with its complete
geometric/coherence argument in the theorem docstring and node. Its auxiliary
maps are explicit categorical compositions.

`lem-sfb-rational-p1-second-scalar-trace` records scalar trace base change from the
normalized unit/Chern splitting, transport through Reference, and coefficient
extension. Its docstring and node explain the finite and closure cases, citing the existing
bounded coefficient-continuity and module/ringed comparison nodes for that transport.

The existing item's proof, proof_deps and proof_origin are updated to the Lean
assembly. No other existing module or node is changed. No change record is
needed because no existing statement, definition or interface changes.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
