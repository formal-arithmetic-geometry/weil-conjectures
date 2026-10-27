## What changed

Proved `AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction.closed_test_localized_adjunctions`
in the assigned module, without changing any existing declaration signature or definition.
The proof establishes ordinary and derived conjugacy for an arbitrary commutative square,
then specializes to all five comparisons in the statement. Five proved private helpers
handle ordinary pasting, derived composition, transitivity of right-derived natural
isomorphisms, derived pasting, and exact localization of the square.

The ordinary calculation uses `CondensedRing.conjugateIsoEquiv_upperStarComp` and equality
induction. The derived calculation uses the existing source-library theorem
`Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`, rather than the proposed
localized-model coherence route. Added three private proof imports for these existing APIs.
Updated step 7, its dependencies, and the proof origin of
`lem-sfb-closed-test-chain-mate-restriction` to describe this proof.

Validation: the cleaned complete module compiled through `lcompile.py` in 43.3 seconds.
All original declarations and their statements remain present. There are no new modules,
public helpers, definitions, statement changes, or forced adaptations.

## Proved and sorry left

Closed one of the three original holes:
`AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction.closed_test_localized_adjunctions`.
Its five conjuncts are proved for the actual specified adjunctions and compositors.

Two original holes remain, with their original statements and proof-plan docstrings:

- `AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction.closed_test_mate_sections`.
- `AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction.closed_test_chain_mate_restriction`.

Both belong to `lem-sfb-closed-test-chain-mate-restriction`. No holes were added or split
off. This is a partial delivery of the module's independent compatibility theorem, not a
proof or decomposition of the main chain-restriction theorem. Net local hole reduction: one.

## No longer needed

Removed unused private proof imports:

- `Sheaf.Paper.ClosedTestUnitEvaluation`.
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.

The first, second, third, fourth and sixth modules remain cited by the retained plans for
the two original holes; their mathematical dependencies have not been withdrawn.

Step 7 no longer needs `lem-sfb-closed-test-localized-model-coherence`
(`Sheaf.Paper.ClosedTestLocalizedModelCoherence`) or
`lem-sfb-derived-composition-adjunction-normalization`
(`Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`). Removed those
two nodes from this node's proof dependencies. Also removed the latter from its obsolete
`tool_uses` entry. These are dependency removals from this item; no claim is made that these
modules are absent from every other target path. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

Step 7's planned specialized localization argument is unnecessary: the asserted pasting
conjugacies hold for every commutative square. The existing ordinary and right-derived
compositor conjugacy APIs prove them directly. No false statement was found, and the unit
route and target statements are unchanged.

Work on the other two holes did not produce a compiling replacement proof. The ordinary
route expands the generic square-mate unit identity, evaluates the direct-image pasting
on sections, and identifies the pulled-back closed-fibre arrow with `testSectionArrow` by
its three pullback projections. The main derived route can use the cochain mate identity
already proved in `Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare`, followed by
naturality of `rightDerivedFunctorUnitQ` and the supplied resolution isomorphism. Its last
clause can use `ClosedTestLocalizedModelCoherence.LocalizedModelEquation` after matching
`localizationUnit` and `localizedRestriction` to the definitions here. None of those
unfinished experiments is included in the delivered Lean module.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
