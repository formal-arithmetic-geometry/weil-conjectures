## What changed

Proved `WeilConjectures.SemilinearSections.openSite_continuous`, `openRing`, and
`openRestriction_exact` in `Sheaf.Paper.SemilinearDerivedCalculus`, preserving all
existing signatures, definitions, visibility, and public imports. Continuity lifts
compatible families to the product slice and pushes forward their vertical covers.
The ring equality uses the identity-component tower transformation constructed by
`NatTrans.ofOpSequence`, then compares its components. Exactness uses cocontinuity
and a private general ringed-site pushforward helper: addition and finite limits are
sectionwise; finite colimits follow from the cocontinuous sheaf adjunction after
forgetting module actions, with reflection through the underlying sheaf functor.

Added proof-only imports of `Mathlib.CategoryTheory.Sites.CoverLifting` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
All writing and compilation used the sandbox and lcompile.py. This continuation
retained the saved proof and checked it against the current source. The final module
compiled cleanly in 13.8 seconds with exit code 0 against the current published
library; delivery preflight also compiles it with its axiom probe.

## Proved and sorry left

Closed three of the original four holes:

- `WeilConjectures.SemilinearSections.openSite_continuous`.
- `WeilConjectures.SemilinearSections.openRing`.
- `WeilConjectures.SemilinearSections.openRestriction_exact`.

The one remaining hole is unchanged:
`WeilConjectures.SemilinearSections.ordinaryEvaluationTensor_existsUnique`
(blueprint node `def-coef-semilinear-derived-calculus`). It still requires the
normalized tensor/sheafification comparison for vertical evaluation, including
uniqueness from the local pure-tensor formula. No holes were added or split off.
The private helper is fully proved.

## No longer needed

None of the original imports, dependencies, nodes, or modules is pruned. The
existing public imports provide the calculus interfaces and are preserved.
No new proof dependency on the ordinary derived calculus or its consumers was added.

## Where the brief, the DAG or earlier work was wrong

The attached node defines the calculus interface and has an empty proof plan;
its helper theorem docstrings provide the relevant proofs in words. The existing
module docstring mentions declarations extracted elsewhere, but this delivery
preserves that documentation and all interfaces. No statement dispute or repair
of a definition was needed.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
