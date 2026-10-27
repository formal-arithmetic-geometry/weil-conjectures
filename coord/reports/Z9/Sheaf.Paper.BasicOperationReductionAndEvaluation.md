## What changed

Replaced the proof hole in `WeilConjectures.basicOperationReductionAndEvaluation`
without changing its statement or its public import. The finite quotient and
ordinary scalar-extension clauses follow from the existing normalized tensor
associativity equations. Private proved categorical helpers establish naturality,
evaluation, transposition and internal composition for these tensor comparisons.
They adapt the categorical calculations already present in
`Sheaf.Paper.FiniteCoefficientHomChange`, without that module's finite-field
geometric hypotheses.

The compact-support proof now transports the specified Roos triangle to a normalized
finite coefficient tower, applies the existing normalized DVR effectivity theorem,
and identifies its counit adjuncts with the specified projection adjuncts. It
transports constructibility and cohomological support across these isomorphisms.
Its transition equality is proved directly from the zero composite in the given
Roos triangle and naturality of the two scalar adjunctions. These categorical
Roos-triangle calculations adapt the proved helpers in
`Sheaf.Paper.IntegralCompactSupportPrescribedReductions`.

For the perfect-source clause, the existing ringed-site perfect scalar Hom theorem
supplies invertibility in its evaluation-normalized model. A new comparison step
identifies that model's map with the fixed finite quotient Hom map. The parent proof
then transports invertibility through explicit natural isomorphisms. Only two
representative-model steps remain as new public theorems in separate modules.

New proof imports are `CoefficientTensorNormalization`,
`CompactSupportNormalizedReductionTower`, `NormalizedDVREffectivity`,
`SfDerivedCompleteLegacyComparison`, `ProEtaleBoundedConstructibleTriangulated`,
`FiniteQuotientHomModelComparison`, `SitePerfectComplex`, and Mathlib's infinite-primes theorem.
An auxiliary finite-field datum with prime characteristic different from l is
constructed to instantiate coefficient-calculus theorems that retain such an index;
no additional geometric hypothesis on a scheme is introduced.

Validation: all three delivered modules compile without warnings, individually in
import order through `lcompile.py --all`. The final timings were 1.7 seconds for
the finite-tower statement, 5.1 seconds for the Hom-model statement and 42.1 seconds
for the parent. The original parent signature was compared token-for-token with
the repository version; the new node signatures match their Lean statements.

## Proved and sorry left

Original direct holes: 1. Closed in the parent module: 1, in
`WeilConjectures.basicOperationReductionAndEvaluation`. Direct holes remaining in
that module: 0. New direct holes: 2:

- `WeilConjectures.compactSupport_normalizedReductionTower`, node
  `lem-sf-compact-support-normalized-reduction-tower`.
- `WeilConjectures.finiteQuotient_homModel_comparison`, node
  `lem-sf-finite-quotient-hom-model-comparison`.

This is a decomposition, not a net proof-hole reduction or a claim that the target's
axioms are already closed. The first residual statement concerns finite levels and
their common bound; it has no limit M, projection p or reduction-isomorphism
conclusion. The actual limit-effectivity argument and transition square are proved
in the parent. The second residual statement identifies two evaluation-defined
maps for arbitrary ambient inputs; it has no perfectness assumption and no
invertibility conclusion. The parent derives invertibility from the existing
site-perfect theorem. Neither residual statement repeats the original obligation.
All private helpers have complete proofs. No definition contains a proof hole.

## No longer needed

No original public import is removed. No existing module or declaration is withdrawn.
No claim of global module pruning is made.

The original omnibus proof-dependency list is replaced by the actual proof route.
The following original direct edges are retained inside the new finite-tower or
Hom-model substeps rather than used directly by the parent:
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-pur-integral-coherence-tower`,
`lem-pur-completed-operation-tower-substitution`,
`lem-weil-pbc-standard-quotients-perfect`,
`lemma-weil-pbc-perfect-projection-formula`,
`prop-weil-pbc-direct-image-limits`, and `lem-sf-open-tensor-normalization`.

The following original direct citations are unnecessary for the written proof:
`lem-sfb-ringed-site-perfect-duality` (encapsulated in the existing scalar Hom
theorem), `lem-weil-l-adic-extension-integers-dvr` (already encapsulated by the
coefficient/tower interfaces), `lem-weil-finite-free-completed-scalar-comparison`,
`lem-sf-ringed-finite-free-hom-base-change`,
`lem-pur-integral-operations-scalar-extension` (the needed tensor associativity is
provided by `lem-sf-coefficient-tensor-normalization`), and
`lem-fix-internal-hom-comparison-composition` (the composition calculation is
proved generically here). Some remain transitively needed by those existing
interfaces and must not be withdrawn on this report's account.

## Where the brief, the DAG or earlier work was wrong

The current queue assigns proof work, despite an older quarantine record. The
published source is present and its original version compiles. Its first clause
quantifies over arbitrary fields with l invertible, whereas the existing
`integralCompactSupport_prescribedReductions` theorem additionally assumes a
finite-field datum, geometric base structures and uniform Tor bounds. Those
hypotheses cannot be silently added; the new finite-tower statement preserves the
arbitrary-field setting.

Adding the apparently convenient integral compact-support constructibility theorem
as a DAG proof dependency would create a cycle through derived direct image,
integral pullback adjunction, operation-exchange realization and this item. The
finite-tower step is therefore stated before inverse limits, and the parent uses
the independent normalized DVR effectivity and completeness interfaces instead.
The revised nodes were checked for return paths to themselves.

Generic tools from other units are used only for coefficient tensor normalization,
normalized tower effectivity, the completeness-predicate comparison,
constructibility's invariance under isomorphism, and ringed-site perfect scalar Hom.
They supply these abstract statements and do not replace any realized statement or
proof step of `sk-prop-sf-pf-reduction`. No maintainer `tool_uses` approval was added.

The old item's blueprint ancestor metadata has a legacy list-shaped `from` field;
`blueprint_refs.py ancestor` cannot follow its module-shaped `created.item`.
The new nodes explicitly cite the existing blueprint node
`lem-fix-operation-reduction`, its precise proof paragraph and this intervening
item. Existing metadata outside the stage-3-owned fields is preserved.

## New nodes

`lem-sf-compact-support-normalized-reduction-tower` is realized by
`Sheaf.Paper.CompactSupportNormalizedReductionTower`. It isolates construction and
uniform bounded constructibility of the finite normalized tower before any inverse
limit. Its docstring records the flat-term representatives, quotient resolutions,
proper projection formula, open-extension normalization and coherent substitution.
Edge cases checked are exponent one, zero input, empty scheme and arbitrary
invertible base field; quotient-ring maps are not assumed flat.

`lem-sf-finite-quotient-hom-model-comparison` is realized by
`Sheaf.Paper.FiniteQuotientHomModelComparison`. It isolates normalization of the
universal derived scalar functor, closed tensor model and evaluation transpose.
Its docstring explains the universal-counit isomorphism and comparison after
uncurrying. It applies to arbitrary inputs, identity quotients, zero objects and
empty schemes, and does not assert invertibility for a nonperfect source.

No existing signature, definition or instance is changed, so no change record or
forced adaptation is required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.BasicOperationReductionAndEvaluation": "b59908be23268f1bf8d538f6d35ec39a1f546105", "Sheaf.Paper.CompactSupportNormalizedReductionTower": "62d3201dc1bdba5188598d565d886564e8cb2d3c", "Sheaf.Paper.FiniteQuotientHomModelComparison": "b932b5f80604bac684c7ba31dc24089400c4a4dc"}, "results": {"Sheaf.Paper.BasicOperationsCoefficientReduction": {"hash": "eaa1b2a943bac48a08b3b7b5f7ae04cf17f6c249", "status": "SLOW"}}, "seconds": 174, "time": "2026-10-28T01:07:10+0800", "transitive": 0, "version": 1}
```

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
