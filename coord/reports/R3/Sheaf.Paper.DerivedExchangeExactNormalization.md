## What changed

Repair of return C-b0e4d (returned head b0e4d0b94dc): compared the retained
reviewed packet with the current shared source. The Lean source still has the three
original holes; the retained proofs close them without any additional module edits.
Rebased the node copy onto the current DAG metadata, retaining its newer review and
split records while applying only this delivery's proof route and approval pruning.
The landing failure named the quarantined source module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`; its archive,
Lean attachments and dependencies are preserved. It is neither restored nor withdrawn
by this packet. Delivery rebases the retained work onto the latest `sheaf-dag`.

Proved the three theorems in `Sheaf.Paper.DerivedExchangeExactNormalization` from the
published canonical constructions. Pullback exactness is transported along its actual
comparison with the termwise functor. The derived-adjunction uniqueness theorem fixes
its normalization and transfers the canonical right-derived shift compatibility.
Existing compositor shift APIs, Mathlib's mate counit identity, and naturality give the
ambient normalization and the triangle morphism, including its connecting square.

For restriction, proved a general identity for full-subcategory mates. For the actual
bounded-constructible construction, identified its three steps with the already proved
`Adjunction.squareExchange` presentation and obtained its counit equation. The fully
faithful restriction API identifies the underlying restricted counits with the ambient
ones; the restricted pullback acts by the ambient map. The square-component hypothesis
therefore gives the same counit equation as the ambient exchange. Injectivity of the
inverse adjunction hom equivalence identifies the two components. A proved private
helper keeps both transformations and square comparisons as parameters during this
calculation. No restricted functor or adjunction is replaced.
A private proved exchange/mate equation transports assertions before component
evaluation. All public definition bodies, public imports, canonical shifts, and theorem
statements are preserved; explicit object and square annotations give their original
inferred types. No source-library module or consumer is changed. The node proof and
change record follow this argument. The change record is
`coord/changes/R3-derived-exchange-local-shifts.md`.

## Proved and sorry left

Closed the three original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedExchange_exact_normalization`.
- `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedExchange_fullSubcategory`.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBaseChangeOfPreserves_app_eq_moduleObjectDerivedExchange`.

All three realize `lem-sfb-derived-exchange-exact-normalization`. Holes closed: 3;
holes added: 0; holes remaining in the delivered module: 0. Split off: 0.
The supplied dependency theorems are used as this stage permits; their transitive
proofs are not claimed closed. The retained full module compiled again without warnings in 29.9 seconds through
`lcompile.py`, using the unchanged limits.
The delivery tool runs the required compile and preflight again before pushing.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`: the existing source exactness
  instances supply the hypotheses; the separate seven-clause wrapper is unused.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact`: the published
  comparison already concerns the actual source K-flat derived functor.
- `Sheaf.CategoryTheory.ExactDerivedComposition`: the actual compositor already has
  the proved shift API; uniqueness of arbitrary composition comparisons is unused.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`.
- `Mathlib.CategoryTheory.Shift.Adjunction`.

The last three imports are redundant with the retained proof imports. The node's proof
no longer uses `det-prop-sfb-module-pullback-exact-main`, `def-sfb-left-derived-exact`,
or `lem-sfb-exact-derived-composition`. The obsolete top-level tool approvals for
`det-prop-sfb-module-pullback-exact-main` and `lem-sfb-exact-derived-composition`
were removed. No module is withdrawn and no adopted source declaration is removed. The
proper-base-change unit route and all ambient and restriction conclusions are retained.

The current DAG's new dependency nodes
`lem-sfb-module-derived-functor-compositor-shifts` and
`lem-sfb-kflat-derived-adjunction-transport-shifts` are not used: their required
conclusions are proved here from the existing compositor, exact comparison, derived
adjunction uniqueness and canonical shift APIs. Their modules are not imported and
the nodes remain available for other consumers.

## Where the brief, the DAG or earlier work was wrong

The prior independent review passed the proof, but landing failed while reading the
quarantined `UpperShriek` source path. The current packet preserves that quarantine
and records the successful fresh compile; the required delivery command performs
the current-base preflight and push.

The planned degreewise compositor proof was already implemented in the source library's
`DerivedCategory.Shift.ExactFunctor`. The canonical adjunction transport is available as
`Adjunction.derived_eq_ofNatIsoLeft`, and the counit equation is `mateEquiv_counit`.
These APIs avoid duplicate proofs and new intermediate holes.

A local private bridge exposes exactly the published pullback shift instance at the
underlying derived-functor type. It ends before the public theorem statements. Local
transparency attributes keep the generic constructions folded during elaboration.
Evaluating the exchange by unfolding it beneath `NatTrans.app` causes costly kernel
reduction; using a proved equation at the natural-transformation level resolves that
cost without changing the data. The preservation predicate is locally exposed for its proof arguments. Explicit `@H`
arguments suppress automatic implicit lambdas at the final helper boundary. In the bounded
calculation, explicitly reducing the small full-subcategory lift, inclusion and functor
composition definitions normalizes hidden object arguments before using the calculated
counit equation. Keeping square comparisons abstract in the proved helper avoids
expanding their large concrete constructions during this normalization. No wall-time
limit or heartbeat budget is raised.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
