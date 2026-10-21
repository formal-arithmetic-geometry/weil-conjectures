## What changed

Repaired the return of branch head `737fd1e48`: removed the unnecessary file-level
warning-suppression option. The landing hole scanner had counted the `sorry` component
of that option's name as an unattributed hole outside a theorem. The complete proof is
retained, with no warning suppression and no proof holes.

The repaired module compiled cleanly through `lcompile.py` (exit 0, 17.1 seconds).
The project's source hole scanner reports exactly the named theorem, zero hole
markers, and no warnings. The theorem signature and all public imports match the
current repository; every Lean line is at most 100 characters. The changed DAG
proof dependencies equal the union of its proof steps and have no path back to
this item.

Added `coord/changes/H1-specified-pullback-warning-option.md` as required by
preflight for the removed file-level command. It records all 13 downstream
modules and the unchanged statement of the sole external textual consumer;
no consumer adaptation is necessary.

Proved `WeilConjectures.specifiedPullbackComparisonAlpha` without changing its statement,
public imports, definitions, or other modules. Added the private proof import
`Sheaf.Paper.IntegralOperationsPreserveConstructible` and removed the obsolete private
proof imports listed below. Updated the item's DAG proof and proof dependencies to
match the shorter proof, and removed its unused Roos-cofinality tool approval.

The existing normalized `scalarPullbackOrdinary_existsUnique` already identifies the
specific localized chain comparison with a composite of isomorphisms. Reflecting this
invertibility through `DerivedCategory.Q` gives the required quasi-isomorphism. The
normalized `scalarCompletion_existsUnique` gives the corresponding completion-chain
argument on complete K. Naturality transports the representative equations along e;
expanding the definition of `scalarPullbackCompleted` and cancelling inverse pairs
proves its formula and the final square. `scalarGood` supplies goodness after scalar
extension, and `integralOperations_preserve_constructible` supplies pullback completeness.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.specifiedPullbackComparisonAlpha`
(node `lem-weil-specified-pullback-comparison-alpha`). Added zero holes and zero new
modules. No `sorry` remains in the delivered Lean file. This is a proof from existing
stated dependencies; in particular the existing normalized comparison theorems retain
their own separately assigned proofs. No dependency theorem is restated or weakened.

## No longer needed

Removed these direct private proof imports:

- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`

The item's proof no longer directly uses these former proof-dependency nodes:

- `lem-pc-kflat-resolution`: the input already quantifies over every good representative.
- `lem-pur-derived-change-of-rings` and `lem-pur-kflat-change-of-rings`: use the proved
  `scalarGood` interface instead of repeating its proof.
- `lem-pur-integral-operations-well-defined`: use the existing representative comparison
  isomorphisms through the normalized scalar comparison theorem.
- `lem-weil-scalar-pullback-strict-cone-naturality`,
  `lem-weil-ramified-pullback-tower-identification`, and
  `lem-weil-roos-transition-homotopy`: invertibility of the specified chain map already
  follows from `scalarPullbackOrdinary_existsUnique` and its normalization equation.
- `lem-weil-proetale-countable-products-exact`: no products are reconstructed here.
- `lem-weil-finite-free-completed-scalar-comparison`: use the already normalized
  `scalarCompletion_existsUnique` and its complete-input invertibility clause.
- `lem-weil-isomorphism-derived-pullback` and `def-weil-derived-pullback-tensor-hom`:
  pullback completeness follows directly from the proved constructibility preservation
  theorem for the same `integralDerivedPullback` functor.

Removed the obsolete `lem-pur-compact-support-roos-cofinality` tool-use entry. These are
removals from this item's direct proof route, not withdrawals of their modules: their
other consumers and transitive uses are unaffected. All eight original public imports
are preserved. No unit statement or realized unit step is bypassed; this item is not
among its unit's realized statement/step nodes.

## Where the brief, the DAG or earlier work was wrong

The returned packet retained a warning-suppression option from the original statement
module. Removing it fixes the reported unattributed-hole finding without changing any
declaration or modifying the project tools.

The planned explicit ramification/Roos homotopy argument duplicates what is already
expressed by the normalized ordinary scalar/pullback comparison's existence as a natural
isomorphism. Its normalization fixes the precise `scalarPullbackChain`, so cancellation
proves the requested quasi-isomorphism without constructing another map or identifying
unrelated endpoint isomorphisms. The original statement is unchanged. The three selected
existing dependency nodes have no dependency path back to this item.

Several remote compile requests received exit 124, with no answer from the busy compile
server. They were retried as instructed; these were not Lean compilation failures.
Compiler diagnostics on completed requests were used to make the representative-object
identification explicit and finish the category equations. The final file compiled
cleanly through lcompile.py (exit 0, 17.3 seconds), with no errors or warnings.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
