## What changed

Prove `WeilConjectures.constantExtensionCyclicSheets` from the existing
`constantExtensionSheetGeometry` package: the coordinate factorization gives the open
immersions, closed ranges give the closed immersions, disjoint covering ranges give the
coproduct, and the last cyclic return equation gives the mth-power identity.

Move the 31 existing data declarations and complete compatibility proofs verbatim to
`Sheaf.Paper.ConstantExtensionWeilHeartData`, publicly reexported by the item. Replace the
parent import of `ConstantExtensionSheetHeartData` by that data import. This breaks the
otherwise unavoidable import cycle through the geometry theorem. Update the existing
DAG definition attachments and add the geometric step to the parent proof plan.
Change record: `coord/changes/H5-constant-extension-data-relocation.md`.

Validation: the three-file sandbox compiles. The successful profiled run took 48.5 s
for extracted data, 46.3 s for sheet-heart data, and 35.7 s for the item. The profile
shows no slow definition: cumulative elaboration 0.8 s, tactics 0.7 s and typeclass
inference 3.1 s. Temporary profiler options were removed before delivery. Source
comparison preserves all 33 old public statements and every old body except the
filled cyclic-sheet theorem. The overlay import closure is acyclic; the newly
added geometric DAG dependency has no path back to the parent.

## Proved and sorry left

Closed 1 of the item's 2 holes: `WeilConjectures.constantExtensionCyclicSheets`.
Added 0 holes; split off 0 statements.
The one hole left is `WeilConjectures.constantExtensionWeilHeartEquivalence`, belonging to
`lem-zl-constant-extension-weil-heart-equivalence`; its statement and proof body are unchanged.
The extracted data module and adapted sheet-heart data module contain zero holes.
The cyclic-sheet proof uses the existing geometric-step theorem, whose existing sorry
remains in `Sheaf.Paper.ConstantExtensionSheetGeometry`; this delivery does not close that
lower dependency.

## No longer needed

No mathematical node or module is pruned. The geometry step remains needed. The parent
import in `Sheaf.Paper.ConstantExtensionSheetHeartData` is replaced by the extracted data
import: that interface uses no declaration of either remaining theorem. The item's
proof-only `Mathlib.AlgebraicGeometry.Morphisms.Finite` import moves with the existing
complete data proofs, which use it. The two original public imports remain publicly
reexported through the data module.

The five existing assembly dependencies of the unfinished main equivalence remain in its
DAG proof plan. None is claimed to be pruned merely because the main proof is unfinished.

## Where the brief, the DAG or earlier work was wrong

The geometric and coefficient assembly lemmas import the item for its definitions.
They cannot be imported back to prove its theorems until data are extracted. The existing
sheet-heart-data node itself notes this pattern, and the recorded review of sheet-return
data also flagged the shared parent module. No mathematical statement has been weakened.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
