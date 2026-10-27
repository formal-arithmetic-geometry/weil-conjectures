## What changed

Filled both proofs in `Sheaf.Paper.SpecifiedHomScalarEvaluationArbitraryScheme`, preserving
all existing signatures, definitions and public imports. The arbitrary-scheme comparison
unfolds `scalarHomCompleted`, cancels the prescribed completion isomorphisms, and uses
`Equiv.symm_apply_apply` for the ordinary evaluation transpose. The completed chain theorem
uses `specifiedHomScalarChain`, whose own statement already applies to arbitrary schemes,
and transports its localization equality through the proved completion cancellation.
The section formula, fixed augmentations, existence and uniqueness are preserved.

Updated the existing node `lem-pod-specified-hom-scalar-evaluation` to record this shorter
route and the existing ordinary chain dependency. No definitions or statements change;
no consumer adaptations or change records are needed. No new nodes were introduced.

## Proved and sorry left

Closed two holes, by declaration:

- `WeilConjectures.specifiedHomScalarEvaluation_arbitraryScheme`.
- `WeilConjectures.specifiedCompletedHomScalarChain`.

Zero holes remain in the item, and zero holes are added or split off. The ordinary chain
result is an existing named theorem, `WeilConjectures.specifiedHomScalarChain`, belonging
to `lem-zl-specified-hom-scalar-evaluation`; its pre-existing proof obligation remains in
its owning module. This delivery does not claim to close that dependency or all axioms
in the transitive import closure.

## No longer needed

Removed these seven private proof imports from the item:

- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor`.
- `Sheaf.Algebra.Homology.ScalarHomChainEvaluation`.
- `Sheaf.Algebra.Homology.OneKFlatChainTranspose`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

The item now needs no private proof imports: its existing public imports already expose
the ordinary chain theorem, the comparison definitions and the required categorical API.
No library declaration or module is withdrawn. In particular these providers may still
be needed transitively by the definitions or the reused ordinary chain theorem.

The old direct proof dependencies no longer used directly by this argument are:
`lem-weil-finite-free-completed-scalar-comparison`,
`def-weil-derived-complete-integral-detailed`,
`lem-sf-ringed-finite-free-hom-base-change`, `lem-pc-kflat-resolution`,
`prop-pur-kinjective-resolutions-exist`, `def-pur-derived-internal-hom`,
`lem-weil-pbc-exact-functor-derived-factorization`, `lem-pur-derived-change-of-rings`,
`lem-sf-ringed-finite-free-tensor-data`, `lem-sfb-scalar-hom-chain-evaluation`,
`lem-sfb-hom-kflat-chain-transpose`, `def-coef-ringed-tensor-hom-model`, and
`def-weil-integral-scalar-extension`. Their representative construction and comparison
work is already encapsulated in the existing ordinary chain theorem or the recorded
comparison definitions; this proof does not reconstruct it. Statement dependencies
are preserved. The node now records the actual direct dependencies
`lem-pur-integral-operations-scalar-extension`, `lem-coef-derived-system-evaluation-calculus`
and `lem-zl-specified-hom-scalar-evaluation`. The unit has no realized node in this route,
and its statement and proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original DAG proposed rebuilding the scalar chain map using general finite-free
base change and K-flat transposition. That work is already stated as the ordinary
`specifiedHomScalarChain` theorem. Its neighboring evaluation theorem has finite-field
and finite-type hypotheses, but the chain theorem itself has neither restriction;
it therefore applies here unchanged. The reused result gives exactly the ordinary
part of this argument, rather than restating either completed theorem under a new name.
The completion identities are actual categorical cancellations using the current
`scalarHomCompleted` definition, so no chain compatibility or normalization is assumed
anew. No false statement or definition repair was necessary.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
