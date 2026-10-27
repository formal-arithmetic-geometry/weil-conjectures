## What changed

Constructed the proper coefficient-reduction transformation by transposing the existing
ordinary-limit realization. The private categorical calculation evaluates this mate from
`integralProperFiniteProjection`, using naturality and the reconstruction triangle identity.
A second proved calculation shows that the adjoint-uniqueness isomorphism between any two
coefficient calculi intertwines their prescribed finite reduction evaluations, using
`unit_projection` and the finite scalar adjunction. These calculations transport the map to
arbitrary `SX`, `SY`, and then to the native direct-image presentation. The final proof cancels
the separately derived `finiteDirectImage_eq` and gives the original ringed-coordinate formula.
The statement and definition of `strictCoefficientProperEvaluation` are unchanged.

Validation: `lcompile.py --all` compiled both sandbox modules successfully.
The original theorem signature and evaluation definition were compared verbatim,
and all Lean lines are at most 100 characters.

The remaining presentation comparison is isolated in a new module. Its statement concerns
only two models of derived sequence direct image and their normalized evaluations; it has no
completed-coefficient input, reduction functor, reconstruction limit, or scalar comparison.
Thus it is a strictly smaller presentation step, not the original reduction assertion under a
new name. The scalar-adjunction construction and the normalization for arbitrary calculi are
proved in this delivery.

Four new definition-interface nodes isolate existing ordinary constructions from broad former
owners that also contained later compact-support realization data. Eleven existing theorem
nodes cite these smaller interfaces. Their Lean files, mathematical hypotheses, conclusions,
and proofs are unchanged. The change record audits every direct DAG citer. These refinements
remove the artificial cycle that otherwise results from using the existing lower realization
lemmas to prove this item.

## Proved and sorry left

Closed the original hole `WeilConjectures.strictCoefficientProperReduction` by a complete
composition proof from existing declarations and the following new hole:

- `WeilConjectures.nativeProperDerivedPresentation` in
  `Sheaf.Paper.NativeProperDerivedPresentation` (one `sorry`). Its docstring and node give the
  section-normalization, universal right-derivation and mate proof.

Original item: 1 hole closed of 1; 0 holes remain in the item. New modules: 1 hole added.
This is a decomposition, with one hole closed and one added among the edited declarations.
The ledger separately accounts for existing obligations exposed by the new imports; no net
ledger progress is claimed here. Existing imported
`WeilConjectures.IntegralSystemRealization.integralProperFiniteProjection` remains an existing
lower obligation; its proof is not duplicated or moved here. All private helpers are proved.
No definition contains `sorry`.

## No longer needed

The item's new proof does not directly use the planned dependencies
`lem-pc-kflat-resolution`, `lem-pur-left-derived-from-kflat-class`, or
`lem-weil-pbc-ring-sheaf-change-adjunction`: the existing normalized realization and finite
projection declarations already encapsulate that work. They are removed from the item's
immediate proof dependency list, not claimed globally unnecessary. Their lower uses remain.
The item's two original public imports are retained because its public statement uses them.
No existing Lean module is withdrawn and no source-library declaration is removed.

For the eleven adjusted lower nodes, the change record lists every broad interface replaced
by the corresponding existing ordinary or finite-coordinate interface. In particular the
proper finite projection needs `properComparison`, `finiteReductionIso` and
`finiteDirectImage_eq`, not the later integral compact-support comparison theorem; ordinary
limit models need actual completed ordinary image, not finite-expression completion data.
These are attachment refinements, not deletion of the declarations in the broad owner modules.

## Where the brief, the DAG or earlier work was wrong

A direct proof from the existing reconstruction and finite-projection results is shorter than
rebuilding the K-flat tensor/pullback construction. The old broad DAG ownership falsely made
these lower ordinary constructions depend on later compact-support realization and hence on
this very item. The replacement interface records retain the same mathematical assertions and
remove that circular bookkeeping dependency. No target statement changes.

The rework row records a transitive import of `SfP1ProjectionTraceFalseTail`. The compiler
restores quarantined dependencies into its private overlay. The chosen evaluation construction
uses the exact cochain-normalized `pullbackTensorDerivedEvaluation`, whose proof does not use
`finiteQuotientPullbackDescent`; that latter declaration occurs only in a different theorem of
the broadly imported `CompletedPullbackTensorComparison` module. This delivery neither uses a
false-tail theorem as a proof nor removes or replaces any upstream declaration.

## New nodes

- `lem-native-proper-derived-presentation`: the one new mathematical obligation, strictly the
  derived-direct-image presentation/evaluation comparison.
- `def-strict-coefficient-pullback-evaluation-data`: existing exact finite evaluation and its
  cochain normalization.
- `def-strict-coefficient-system-operation-data`: existing strict-system operation data before
  completed/constructible realization.
- `def-strict-coefficient-system-realization-data`: existing ordinary-limit and normalized
  K-flat reduction realization interfaces, excluding later finite-expression interpretations.
- `def-strict-coefficient-completed-image-data`: actual ordinary completed-coefficient image
  and its finite-projection-normalized coefficient map.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
