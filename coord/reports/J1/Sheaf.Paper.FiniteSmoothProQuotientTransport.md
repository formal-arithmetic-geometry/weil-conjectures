## What changed

Replaced the sole hole in `Sheaf.Paper.FiniteSmoothProQuotientTransport` by a direct
categorical transport argument for all five specified quotient cocycles. The public
theorem signature and the existing public import are unchanged. Added only private
proved helpers and private proof imports, and updated the owning node's proof route.
No other existing module is changed. A declaration-local unused-variable lint
setting preserves the original unused `hY` and exceptional-hypothesis `hn` binders
verbatim.

The proof uses the published site/scalar composition equation, transposes it through
the comparison adjunction to prove origin composition, and proves the common transport
and endpoint-conjugation calculations. Pullback and purity-source endpoints cancel on
the actual scalar-extended Ctf domain. The exceptional equation uses the ordinary
mate's naturality. Compact support uses naturality and cancellation of the actual
bounded-below compact site comparisons, followed by the ordinary compact cocycle.

The full module passed the assigned remote single-file compiler in 32.1 seconds
with zero errors. Profiling options used during development were removed before
delivery. The first delivery probe also compiled in 33.0 seconds; it stopped only on unused
binders in the fixed statement. The declaration-local lint setting resolves those
warnings without changing any binder. The delivery tool repeats compilation and
the required preflight checks.
A static comparison confirms that the public theorem signature is byte-for-byte
unchanged and all lines have at most 100 characters.

## Proved and sorry left

Closed 1 of the 1 original holes:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothProQuotientTransport`
(node `lem-pur-finite-smooth-pro-quotient-transport`). This is a proof from existing
declarations, not a decomposition. Added holes: 0. Split-off statements: 0.
Remaining holes in the delivered module: none (0). All private helpers are proved.
Imported named statements retain their existing proofs and trust status; no axiom
is introduced.

## No longer needed

No separate proof import of
`Sheaf.SecSmoothPurity.ReductionCompatibilities` is needed: its scalar-origin
counit conclusion follows here from quotient Ctf preservation and the intrinsic
origin counit, both already used elsewhere in the proof.

No original Lean import is removed: the sole public import supplies the statement's
canonical maps. No module is withdrawn, and the unit's route is preserved.

The owning node no longer needs separate proof edges to
`lem-weil-pbc-comparison-pullback`
(`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`) or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`). Its pullback and tensor
maps are already fixed in the statement. Their naturality, rather than a fresh
geometric construction of either comparison, is enough for transport. Some of these
modules remain transitively needed by the definitions or other library declarations;
this delivery does not claim they disappear from the targets' full import closure.

## Where the brief, the DAG or earlier work was wrong

The existing plan is valid but its direct proof-dependency list did not name the
already available `comparisonScalarComp`, intrinsic-origin, and quotient Ctf preservation results. Those published results supply the geometric
inputs, so no further split of this previously split obligation is needed. The
proof route now records those exact dependencies. No statement or definition repair
is made. Equal quotient indices are covered by the same associator and counit
identities; no strict inequality or flatness assumption is introduced.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
