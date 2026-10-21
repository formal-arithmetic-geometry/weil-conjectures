## What changed

Restored the quarantined module `Sheaf.Paper.ContinuousIntegralPullComposition` with
its complete archived proof of
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp`.
The live path was absent under the assigned rework row. The public theorem signature,
coefficient and characteristic hypotheses, public imports, definition bodies and private
helper names are preserved. Neither archive nor DAG attachment is withdrawn.

Repaired the retired exact-right comparison lemma reference in `comp_map_fac`, using
`Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac` and
`Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'` from the proof-only import
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`.
The shorter proof removes unused K-injective resolution assumptions from private helpers.
Concrete normalization uses a fixed-functor unit equation and `Iso.eq_inv_comp` rather
than an open-ended rewrite, and reduces the final bounded-category equality explicitly.
Local reducibility attributes and the canonical local Profinite size instance support
elaboration without changing exported attributes or definitions.

The proof retains the node's three steps: the underived restriction/pushforward square,
its right-derived square by the specified units and K-injective representatives, and
adjunction conjugation followed by the faithful bounded-constructible restriction.
Only the node's proof description and proof-origin note change. No unit route changes.
Validation: the complete delivered source compiles cleanly through lcompile.py in
45.3 seconds, within the unchanged 60-second single-file limit. The final source has
no diagnostic options, warnings, sorry tokens, or lines exceeding 100 characters.
A token comparison confirms the original public theorem signature and all public
imports are unchanged.

The unchanged archived direct consumer
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` also compiles against this
restoration in 41.5 seconds. Its existing line-length warnings were observed in the
scratch check; no consumer file is changed or delivered.

The imported-artifact axiom check reports propext, Classical.choice, Quot.sound and
sorryAx for the restored theorem. A dependency traversal traces the latter into existing
published dependencies, including ProEtale.isMonoidal_lowerStarComp,
CondensedRing.preservesKFlatQuasiIso_upperStar and generated proof auxiliaries of the
existing lower-star, left-derived upper-star, bounded upper-star and integral pull
comparison definitions. The repaired exact-right factorization theorem, the derived
composition conjugation theorem, and integralScalarExtension_exact individually use
only the three allowed axioms. The restored module adds no direct sorry; this delivery
does not claim that its full published dependency closure is already sorry-free.

The change record is
`coord/changes/P4-restore-continuous-integral-pull-composition.md`.

## Proved and sorry left

The restored public theorem is completely proved:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructiblePullIso_comp`
(node `lem-weil-pbc-continuous-integral-pull-composition`). All private helpers are proved.

The authoritative archived source already had zero sorry holes. This restoration repair
therefore closes 0 of 0 existing holes and adds 0 holes; 0 holes remain. No statement is
split off, no axiom is introduced, and no definition contains a postponed proof or data.
This is a missing-module/API repair, not a claim of newly closing the historical hole.

## No longer needed

None. All archived imports, helper names, declared node dependencies and both parent
DAG obligations remain. The new factorization import supplies both theorems actually
used by the repaired proof. No module or node is withdrawn or pruned.

The search for a shorter route found only ordinary module pullback composition and
adjunction conjugation infrastructure: LeanFinder returned eight ordinary presheaf,
sheaf and scheme-module pullback composition results, and Loogle found
`CategoryTheory.conjugateEquiv_comp`. Neither directly states the specified derived
coefficient comparison equality. A local source search did identify the current proved
exact-right factorization API, which replaces the stale archived proof reference.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, not withdrawn, and already contains a complete proof.
The current library no longer exports
`Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived_eq`, so the archive
cannot be restored verbatim. Its replacement uses the actual canonical comparison unit;
no mathematical statement or planned proof step needs correction.

Initial diagnostic compiles exceeded the single-file time limit. Profiling with lower
heartbeat bounds located expensive matching of concrete derived-functor expressions in
the adjunction-factorization rewrite and final bounded-category normalization. The
repaired proof uses explicit factorization and targeted reductions. Diagnostic profiler
settings are removed from the delivered source, and the compile time limit is unchanged.

The live downstream scan is empty because the consumers are themselves quarantined.
The change record therefore also traverses the quarantine import graph and lists all
nine archived consumers. Both immediate consumers retain the same theorem and helper
interfaces; no consumer adaptation is part of this delivery.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
