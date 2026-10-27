## What changed

Proved three of the four existing compatibility theorems in
`Sheaf.Paper.FiniteAdjointMateCompatibility`. All three clause definitions and all four
public theorem signatures remain byte-identical. Added one proved private helper,
`finiteMate_noetherian`, for Noetherianity of finite-type schemes over the standing field.
No other Lean module, source-library declaration, or target changes.

The tensor clause reuses the proved generic finite-ring `tensorCompatibility` through
`import all Sheaf.Paper.ExceptionalCoefficientComparison`. This proof-only import also
provides the normalized compact-support and exceptional-mate helpers. Their generic
finite-ring proofs apply directly to the actual lifted coefficient quotients.

Arbitrary Cartesian base change uses the proved `compact_scalar_exchange_left` helper,
inverts its compact-support coefficient square, and applies
`coefficient_exchange_of_counit_at`. The source-library smooth exceptional finite-Tor
preservation theorem gives a lower bound for the exceptional image. Finite Tor gives
its scalar extension a lower bound without a flat quotient assumption. The transpose
clause follows directly from naturality and `unit_mateEquiv`.

The composition theorem remains its original named `sorry`, with its original complete
proof docstring. At the first delivery round, the attempted composition proof had a
proved abstract mate-pasting calculation, but matching the concrete derived functors
exceeded recursion depth and then the fixed compile limit. That uncompiled attempt
and its unused private helpers are omitted. No limits are raised in the delivery.

Updated the DAG proof and dependencies for the three proved clauses; preserved the
original composition proof step and its dependencies. Validation: tensor, arbitrary base change, transpose and the Noetherian helper each
elaborated successfully in earlier server runs. The final partial packet could not
be compiled: lcompile.py and deliver3.py both failed before Lean ran because the
compile service could not create a temporary directory (No space left on device).
The normal retry gave the same failure. Nothing was pushed; final preflight is pending.

## Proved and sorry left

Closed three original holes:

- `WeilConjectures.PurityFiniteSetting.finite_adjoint_mate_tensor`.
- `WeilConjectures.PurityFiniteSetting.finite_adjoint_mate_baseChange`.
- `WeilConjectures.FiniteExceptional.finite_adjoint_mate_transpose`.

One original hole remains:
`WeilConjectures.PurityFiniteSetting.finite_adjoint_mate_composition`, owned by
`lem-pur-finite-adjoint-mate-compatibility`. Its signature and original proof plan stay.
Holes added: zero. Split-off statements: zero. The private helper is proved.
Imported statements keep their existing proof obligations.

## No longer needed

Removed direct imports:

- `Sheaf.Paper.ExchangeProjectionSuppliedDomains` (formerly public).
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`.

Removed proof dependencies `def-exchange-projection`,
`lem-fix-compact-support-coefficient-change`, `lem-fix-operation-reduction`,
`lem-sf-proetale-constructible-origin`, `lem-weil-finite-compact-projection-formula`,
and `thm-cbc-finite-level-proetale`. The existing ordinary-etale generic helpers supply
the actual equations used by the three proofs. Statement dependencies are preserved.

`Sheaf.SixFunctors.CompactCoefficientComposition` stays publicly imported for its
`finiteCompositionCoefficient` instance and remains a dependency of the unfinished
composition plan. `Sheaf.SixFunctors.FiniteExceptional` remains necessary for the
fourth theorem's intrinsic pro-etale functors, adjunction and q/b definitions.
No module is withdrawn; no global pruning claim is made for other consumers.

Removed five obsolete top-level tool-use approvals:
`lem-fix-operation-reduction`, `lem-fix-compact-support-coefficient-change`,
`lem-weil-finite-compact-projection-formula`, `lem-sf-proetale-constructible-origin`,
and `thm-cbc-finite-level-proetale`. Retained the approvals for
`lem-coef-finite-exceptional` and `lem-sf-compact-coefficient-composition`, which the
unfinished composition plan still uses. New proof tools include
`lem-weil-pbc-coefficient-exchange-mates` and
`lem-weil-pbc-finite-type-over-noetherian`; approvals are left to the maintainer.
The unit's statement and realized proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The proved generic finite-ring
private helpers already handle the actual coefficient rings, although their public
wrapper specializes to Z/l^r. Thus the tensor and base-change proofs need no new
origin witness or pro-etale comparison construction. The transpose equation follows
from b's defining mate, without the separately bundled unit-normalization theorem.
The remaining composition elaboration issue is recorded above; it is not claimed
as a proof or a broken compilation tool.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
