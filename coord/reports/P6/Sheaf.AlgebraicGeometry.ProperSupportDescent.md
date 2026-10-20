## What changed

Completed the retirement assigned by `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.ProperSupportDescent`. Its already-proved declaration
is duplicated by `WeilConjectures.AlgebraicGeometry.ProperSupportDescent`.
The upstream statement has the same name, universes, remaining arguments and
conclusion, and omits only the unused Noetherian-ring instance.

Withdrew the Sheaf module through `deleted.txt`; the delivery tool represents
withdrawal as an empty module. Updated the Lean attachment of
`lem-pc-proper-support-descent` to the upstream declaration, including its exact
signature and a note explaining the sole API difference. The node's statement,
four proof steps and proof dependencies are unchanged: the upstream proof uses
the same scheme-theoretic support, support-pullback, closed-subset-properness and
eventual-properness results. The unit route remains intact.

The retirement table's former consumer `Sheaf.AlgebraicGeometry.ChosenModuleFlatProperStage`
is already retired. Its node `lem-pc-chosen-module-flat-proper-stage` is attached to
`WeilConjectures.AlgebraicGeometry.ChosenModuleFlatProperStage`, which already
imports and applies the upstream theorem. No consumer edit is needed.
No adopted-source file or target statement is changed.

Validation through `lcompile.py`: compiled the upstream theorem and its unchanged
upstream consumer; also compiled an example with the complete old signature by
directly applying the upstream theorem. The example succeeds and `#print axioms`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The example retains the Noetherian-ring instance, demonstrating that the node's
original statement follows without a signature adaptation or any new theorem.
Searches of `lean/` and `quarantine/` find no remaining importer of the retired
copy; `tools/downstream.py` reports zero downstream modules.

Change record: `coord/changes/P6-proper-support-descent-retirement.md`.

## Proved and sorry left

Zero holes before and zero holes after. No holes closed or added; no split-off
statements. This is a duplicate retirement, not a new proof or decomposition.
The existing upstream theorem
`AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit`
(node `lem-pc-proper-support-descent`) proves the original statement and uses only
the three permitted axioms. The delivered withdrawal contains no declarations
and no sorries.

## No longer needed

Retired module: `Sheaf.AlgebraicGeometry.ProperSupportDescent`.
Its duplicate local declaration and all ten imports disappear with the copy:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.RingTheory.Noetherian.Basic`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `WeilConjectures.AlgebraicGeometry.EventuallyProper`
- `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `Sheaf.Paper.SchemeTheoreticSupport`
- `WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier`

These mathematical dependencies remain used by the adopted upstream proof;
none of the four proof-dependency nodes is pruned. In particular, the parent
node continues to cite `lem-pc-proper-support-descent`; its argument now uses the
upstream theorem through the updated attachment. Zero current importers alone
is not the basis for retirement: the explicit retirement request and the
already-adapted upstream consumer provide the replacement argument.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a module containing a hole, but this item is
a listed retirement and has been proved since the B3 landing. The obsolete Lean
attachment still named the duplicated Sheaf declaration after upstream adopted
its proof. The kept-pairs table calls the upstream signature different; the only
difference is its omitted Noetherian-ring instance, as the compiled old-signature
example confirms. No mathematical correction, new node or change to a unit is
required.

LeanFinder returned affine-transition-limit lemmas rather than this statement;
Loogle rejected the unqualified `IsProper` search identifier; Mathlib grep found
no direct support-descent theorem. The decisive existing result is the adopted
upstream theorem found by source search, whose full proof was inspected.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
