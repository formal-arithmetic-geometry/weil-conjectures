## What changed

Proved `AlgebraicGeometry.Scheme.strictQuotientPullbackComputation` in
`Sheaf.Paper.StrictQuotientPullbackComputation`, preserving every existing signature,
definition body and docstring. Added proved private generic helpers for cochain counit naturality and
transporting commutative squares through functors and isomorphisms. The proof reuses
existing private APIs through proof-only `import all` of CompletedTowerPullback and
AdicCoefficientDatum. No source-library module is changed.

The shorter route uses the existing exact completed tower pullback, its universal
counit uniqueness, and the existing quotient change-of-rings quasi-isomorphism lemma.
It constructs delta and chi from the specified counit and proves every augmentation,
comparison, cocycle, naturality and inverse-naturality clause by cancellation.
The theorem's DAG proof, proof dependencies and proof origin follow this route.

To reduce repeated kernel unfolding, changed `cbcStrictReduction`, `cbcStrictDelta`,
`cbcStrictPull` and `cbcStrictCounit` from abbreviations to regular definitions.
Their full bodies and types are unchanged. The only explicit unfolding newly
needed in the proof is at constant-complex quasi-isomorphism instance search.
Change record: `coord/changes/F3-strict-quotient-alias-reducibility.md`.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.Scheme.strictQuotientPullbackComputation`
(node `lem-cbc-strict-quotient-pullback-computation`). Added zero holes; zero holes
remain in the delivered module. No split-off statements or new nodes.

Validation: `lcompile.py --all` compiled the item in 37.7 seconds and all four
unchanged downstream consumers in 29.5–36.7 seconds against its compiled overlay.
Temporary consumer copies were removed from the delivery. The required delivery
compile/probe is the final gate.
The final proof compiled again in 29.5 seconds after replacing two rewriting
steps by direct equality composition. A temporary check with the delivery
axiom-probe code also completed with `SHEAF-PROBED 42` and no disallowed axioms.
The proof uses the existing `exactComplexCounit_isIso` API. The local irreducibility
attribute on the reduction tower functor avoids unnecessary unfolding within this
proof only. Consumer checks are recorded with the alias change.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` (the existing
  `reductionChange_quasiIso` API already supplies the required special case).
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.

The last two are unnecessary for this theorem because the existing completed
pullback is exact. Their upstream declarations and all other uses remain intact.

The current node's declared proof dependencies
`lem-cbc-strict-coefficient-augmentation-homotopicality` and
`lem-cbc-localized-counit-augmentation-calculus` are not used: the published strict
augmentation is already natural, and the required special case of the counit
calculus is proved directly. Their modules
`Sheaf.Algebra.Homology.StrictCoefficientAugmentationHomotopicality` and
`Sheaf.CategoryTheory.LocalizedCounitAugmentation` are not imported.

Removed node proof dependencies and obsolete tool approvals for
`lem-pur-left-derived-from-kflat-class` and
`lem-weil-pbc-diagram-kflat-replacements`. Retained the change-of-rings tool approval
and recorded its actual use. No module is withdrawn; pruning here describes this
item's dependency edges, not a claim of global unreachability.

## Where the brief, the DAG or earlier work was wrong

The DAG plan predates the existing exactness proof for completed pullback and
therefore requests a resolving-class argument that is no longer necessary.
`completedTowerModulePullback_finiteLimits` and its finite-colimit counterpart,
and `exactPullbackCounit_isIso` already provide the relevant exact-pullback API
(the proof uses all three). The quotient levels are not assumed flat;
`reductionChange_quasiIso` uses K-flatness of the representatives instead.
The unit record has no realized steps; its statement and route are unchanged.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
