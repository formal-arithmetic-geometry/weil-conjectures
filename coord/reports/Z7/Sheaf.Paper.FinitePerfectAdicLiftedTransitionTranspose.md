## What changed

Added `Sheaf.Paper.FinitePerfectAdicLiftedTransitionCanonicalTranspose`, which states the
canonical derived-restriction transpose as a strictly simpler intermediate obligation.
Its proof is left as the named theorem required by the stage-3 decomposition policy.
The assigned module now imports that intermediate theorem and proves the original theorem
for an arbitrary supplied left adjunction. The proof uses
`ModuleCat.derivedRestrictScalars_isRightAdjoint`, `Adjunction.leftAdjointUniq`, and the
unit equation for the uniqueness isomorphism. No target signature or definition changed.
The parent DAG node now records the intermediate proof dependency and the actual
left-adjoint-uniqueness route.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.finitePerfectAdicLiftedTransition_transpose_isIso` in
`Sheaf.Paper.FinitePerfectAdicLiftedTransitionTranspose`.

Added one strictly simpler split-off theorem, with one remaining `sorry`:
`AlgebraicGeometry.Scheme.finitePerfectAdicLiftedTransition_canonical_transpose_isIso`
(node `lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose`).
The split isolates only the canonical left adjunction supplied by the derived scalar
restriction API; the delivered parent proof from that statement is complete. No sorry
was added inside a definition.

## No longer needed

The original parent proof plan named
`def-weil-pbc-finite-perfect-adic-tower-data` and
`def-weil-pbc-finite-perfect-adic-constant-normalization` directly. The delivered parent
proof uses them through the canonical-transpose intermediate node, so they were removed
from that node's direct `proof_deps` and replaced by
`lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose`.
They remain needed by the intermediate statement and module; no declaration or module is
pruned. The assigned module's original public import remains needed for its statement,
and the only added import is the private proof import of the new intermediate module.

## Where the brief, the DAG or earlier work was wrong

The existing DAG treated transport through the universe lift and transport from the
canonical derived restriction adjunction to an arbitrary supplied left adjunction as one
step. The latter is elementary and is now proved in Lean via `leftAdjointUniq`; the former
is isolated as the strictly simpler canonical-transpose statement. The original theorem
statement, hypotheses, and unit route are unchanged.

## New nodes

`lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose` records the
canonical derived-restriction transpose. Its Lean declaration is in
`Sheaf.Paper.FinitePerfectAdicLiftedTransitionCanonicalTranspose`; its remaining proof is
the universe-lift transport described in the theorem docstring. No change record is
needed because this delivery changes only the assigned module, a new Sheaf module, and
DAG records.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicLiftedTransitionCanonicalTranspose": "4a8d1d12fa0a9bc0495186149048e47503906642", "Sheaf.Paper.FinitePerfectAdicLiftedTransitionTranspose": "04468a58b8bbfc9b25fbf5c38ef60f08629cb0e3"}, "results": {"Sheaf.Paper.FinitePerfectAdicLiftedTransitionUniversal": {"hash": "bbfa7f6b201938b3c89f6d1047c3a7233bbb83d7", "status": "OK"}}, "seconds": 14, "time": "2026-10-28T08:14:32+0800", "transitive": 0, "version": 1}
```

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
