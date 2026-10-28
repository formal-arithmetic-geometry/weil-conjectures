## What changed

Proved `AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_realizations` in
`Sheaf.Paper.FinitePerfectAdicCoordinateRealizations`, with its statement unchanged.
The proof constructs every actual comparison by composing the supplied descent
comparison with explicit exact-functor comparisons. It adds six proved private
helpers for normalization, chart restriction, and the sheafification counit.
The only added import is a private `import all` of
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicLisseFixed`, to use its existing
constant-scalar restriction construction. Existing public imports are retained.

Compatibility with the completed scalar map forces normalization of phi on all
quotient scalars: every quotient scalar lifts to A. The composite chart site functor
is naturally isomorphic to the slice forgetful functor. The associated-module
sheafification counit then cancels the finite-scalar restriction. Exact derived
composition transports this ordinary comparison. Finally the existing
`completedAdicFiniteReduction_comparison` and the derived-evaluation factorization
identify the result with the level of the exact strict representative in the goal.

The argument uses no boundedness of M, no geometric point, and no nonzero
coefficient or nonempty-chart assumption. Zero quotient rings and empty charts
are covered by the same functors and invertible counits. No data is chosen from
an unproved mere-existence theorem. The isomorphism-class choice in the existing
finite-reduction comparison is used only as an isomorphism in a theorem proof.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_realizations`
(node `new-w5-finite-perfect-adic-coordinate-realizations`).

Added 0 holes. There are 0 remaining `sorry`s in the delivered module and no new
modules or nodes. All six private helpers are proved. This is a proof, not a
decomposition. The complete module compiled remotely with exit code 0 in
30.9 seconds. Delivery preflight performs the final checks.

## No longer needed

The existence theorem `finitePerfectAdic_marked_origin` is not used: the item's
hypotheses already supply K and its comparison. Its module remains necessary
for `finitePerfectAdicQuotientCoordinates` and the statement's coefficient data.
The scalar-transition coherence theorem and its compositor are not needed to
construct individual realizations. Their existing public import is retained as
part of the module's public interface, also used by the transition assembly.
Accordingly the original proof dependencies
`lem-weil-pbc-finite-perfect-adic-marked-origin` and
`lem-weil-pbc-finite-perfect-adic-scalar-coherence` are replaced by the actual
normalization, exact realization, localization, and strict-reduction dependencies.
No whole module is withdrawn or claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The old two-step plan cited marked-origin existence and consecutive scalar
coherence, but neither statement gives the cancellation comparison required here.
There is no need to split that comparison again. The existing associated-module
sheafification counit and the already proved finite-reduction comparison suffice.
The hypothesis hcompat, specifically its completed-scalar square, is what connects
the supplied phi to the canonical scalar presentation. Neither hphi nor hKplus
is needed once e and this compatibility are supplied; their binders are preserved.
The unit statement and route are unchanged.

Separate finding for the maintainer: STATEMENT-DISPUTED:
`finitePerfectAdic_coordinate_transition_coherence` quantifies over arbitrary dK
and arbitrary actual, without a defining lifted-square hypothesis. Taking dK=0
makes its left side zero. On a point with A=F_2, I=0 and a nonzero constant
single-degree module, the strict quotient transition is an isomorphism, so its
right side is an isomorphism between nonzero objects and cannot be zero.
This neighboring statement is not imported as a proof dependency or used here.
Its repair belongs to the separate assigned coherence item; this delivery does
not change that module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicCoordinateRealizations": "b99bb7cea01a02185a44d287c9a13d2466afdde6"}, "results": {"Sheaf.Paper.FinitePerfectAdicCoordinateTransitions": {"hash": "d9fa0c59926aca9846475834931b5302e3b5fd15", "status": "OK"}}, "seconds": 53, "time": "2026-10-28T10:29:44+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
