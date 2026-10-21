## What changed

Completed all three theorem proofs in
`lean/Sheaf/Paper/SfConstructibleCanonicalCompleteness.lean`.
First obtain tower completeness from `pbcIntrinsicComplete_towerComplete`.
For arbitrary generators and representatives, the normalized
`completedKoszulQuotientComparison` equation identifies the unit followed by an
isomorphism with `d.completionUnit`; cancel that isomorphism using
`isIso_comp_right_iff`. Specialize to the reflector's canonical representative.
For integral objects, use the first membership condition `M.property.1`.
This is exactly the existing four-step DAG plan; no node update is necessary.

Trimmed redundant or unused public imports, as recorded in
`coord/changes/G2-sf-canonical-completeness-imports.md`. No existing signature,
definition, docstring, universe, or target changed. No consumer adaptations.
Both the initial proof and the final trimmed module compile through lcompile.py
without errors or warnings (final Lean compile: 2.6 seconds).

## Proved and sorry left

Closed all three original holes:

- `AlgebraicGeometry.Scheme.sfConstructibleCanonicalCompleteness`.
- `AlgebraicGeometry.Scheme.sfConstructibleCanonicalReflectorComplete`.
- `AlgebraicGeometry.Scheme.sfIntegralConstructibleCanonicalCompleteness`.

Zero holes remain in the delivered module. Zero holes added; zero split off.
The proof uses existing dependency declarations and their original interfaces.
No new theorem or definition is introduced.

## No longer needed

Removed direct public imports:

- `Sheaf.Paper.AdicCoefficientDatum` (already public through IntrinsicCompletion).
- `Sheaf.Paper.CompletedConstantCoefficientEquivalence` (its interface is not used
  directly; the existing witness-to-tower theorem handles that transport).
- `Sheaf.Paper.IntrinsicCompletionCompleted` (already public through IntrinsicCompletion).
- `Sheaf.Paper.IntrinsicCompletion` (already public through WeilCompletedTensorReflector).
- `Sheaf.Paper.PbcQbarCompletedPullback` (the argument uses the actual integral
  tower unit from CompletedPullback, with no Qbar scalar descent).

The two private proof imports are both used. Every declared DAG proof dependency
is still needed: the recorded completed-pullback node is used through its strict
tower interface, not its additional Qbar specialization. No node, declaration,
or source-library module is withdrawn. Removed direct imports do not assert that
these modules are globally unreachable from the project's other targets.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing reviewed plan fits the
published declarations exactly, including the normalized augmentation and the
canonical representative. The initial file included unnecessary public imports.
The general argument requires no nonempty generating list, nonzero object,
properness, or extra scheme hypothesis, so the stated edge cases are preserved.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
