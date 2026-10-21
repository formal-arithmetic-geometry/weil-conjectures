## What changed

Filled the proof of `SheafOfModules.flat_coefficient_reduction_adjunct` without changing
its signature, any existing definition, or the comparison structure. The canonical derived
map is the inverse composition comparison followed by extension of the restriction-adjunction
counit. Its adjunct formula follows from the normalized composition unit and the triangle
identity. K-flat computation proves its representative and invertibility; associativity and
unit naturality prove all three coherence fields.

Added `Sheaf.Algebra.Homology.OrdinaryFlatCoefficientComparison`, with the ordinary balanced
comparison and its section normalization. The proof constructs its restricted inverse from
sheaf tensor cancellation and the assumed multiplication isomorphism, and reflects
invertibility through restriction. This ordinary result requires no flatness.

Updated the item's DAG proof and dependencies to this argument. Existing public imports
and all existing public signatures remain unchanged. Both modules were checked through
`lcompile.py`: the ordinary module compiled in 25.7 seconds and the final item module
in 24.8 seconds, with no errors or warnings. Existing definition bodies are unchanged.

## Proved and sorry left

Original hole closed: `SheafOfModules.flat_coefficient_reduction_adjunct` (1 of 1).
New theorem proved: `SheafOfModules.ordinary_flatCoefficientComparison`.
No holes added, no holes left in either delivered module, and no unfinished lemma split off.
All private helpers are proved. These proofs use existing declared dependencies; their
own remaining obligations are unchanged.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.

The proof uses the independent-coefficient cancellation lemma
`lem-pur-change-of-rings-tensor-cancellation-independent` in place of
`lem-pur-change-of-rings-tensor-cancellation`. The latter's coefficient universe does not
match the item. `lem-pur-kflat-change-of-rings` and
`lem-weil-pbc-site-derived-tensor-descent` are unnecessary: coherence is categorical,
and invertibility is transported through a K-flat resolution directly.
`lem-pur-derived-change-of-rings` and
`lem-sfb-successive-derived-quotient-normalization` are not invoked as existence theorems:
the input Presentation/Normalization data supply the computations and equations.
The old public cochain-model import is retained as part of the existing public interface;
no withdrawal of that module is claimed. The localization universal-property and exact
functor nodes remain used through their Mathlib APIs.

Obsolete tool-use entries removed, preserving the order of retained approvals:
`def-pur-sheaf-tensor-product`, `lem-pur-change-of-rings-tensor-cancellation`,
`lem-pur-derived-change-of-rings`, `lem-pur-kflat-change-of-rings`, and
`lem-sfb-successive-derived-quotient-normalization`. Tensor/sheafification dependencies of
the ordinary argument now occur on its own node. No library declaration or module is deleted.

## Where the brief, the DAG or earlier work was wrong

The original plan's cancellation declaration fixes a larger coefficient universe; the
independent-coefficient version is the applicable declared result. The original descent
and repeated K-flat-extension steps are avoidable once the derived comparison is defined
by its canonical counit. No mathematical statement was weakened or repaired. The unit's
realized statements and steps are untouched.

## New nodes

`lem-pbc-ordinary-flat-coefficient-comparison` records the strictly ordinary balanced
coefficient comparison, now proved in its own module. Its source is Stacks 03EK and 05V4,
and its proof includes the normalized pure-section formula and reflects invertibility
from the restricted tensor cancellation. There is no new sorry. The change record
`coord/changes/flat-coefficient-reduction-proof-context.md` documents the file-level proof
commands requested by preflight; no existing statement or definition changed. Blueprint searches for tensor cancellation
and balanced comparisons found no duplicate: the ordinary-module Kunneth quotient comparison
is a different specialization. The new node records its nearest blueprint ancestor and the
intervening flat coefficient reduction node.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
