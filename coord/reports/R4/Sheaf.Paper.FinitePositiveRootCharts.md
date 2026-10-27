## What changed

Reduced `existsUnique_finiteTensorSheafCharts` to an explicit construction and two
strict intermediate theorems. Existing public declarations, statements, definitions
and public imports of `Sheaf.Paper.FinitePositiveRootCharts` are unchanged.

`Sheaf.Paper.FinitePositiveChartRecursion` constructs the zero ordinary chart from
the realization unit/counit and constant-module unit comparison. Its ordinary
positive chart recursion uses the given first chart and the inverse existing signed
products followed by tensoring charts and the unit unitor. It selects no arbitrary
witness of a mere existence theorem. The stated normalization theorem concerns
this explicit recursion alone.

`Sheaf.Paper.FinitePositiveChartFrameExt` states extensionality for two arbitrary
maps from one positive line to an arbitrary coefficient sheaf, using agreement on
compatible ordered frame generators. It asserts neither existence nor uniqueness
of a chart family. The item now constructs its candidate, proves its normalization
from the recursion lemma, and proves equality of any competing candidate degree
by degree using the frame extensionality lemma, `Iso.ext`, and `funext`.

Both supporting modules are private proof imports of the item. The DAG records
this argument. The unit route remains the finite-reduction twist compatibility.

## Proved and sorry left

Closed one existing hole by decomposition:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorSheafCharts`
(node `def-pur-finite-positive-root-charts`). No `sorry` remains in the item.

Added two strictly intermediate holes:

- `WeilConjectures.PurityFiniteSetting.finiteTensorOrdinaryChartRecursion_normalized`
  (`lem-pur-finite-positive-chart-recursion`): the section formula of an explicitly
  defined family, proved in words by induction on its tensor recursion.
- `WeilConjectures.PurityFiniteSetting.finiteTensorPositiveChart_frame_ext`
  (`lem-pur-finite-positive-chart-frame-ext`): equality of arbitrary maps from a
  single line to an arbitrary target, proved in words on compatible generators
  and by sheaf separatedness.

This is a decomposition, not a net hole reduction: one closed, two added.
The first-chart theorem was already proved in the refreshed shared source by U5;
this delivery preserves that proof and does not count it as newly closed.

Both remaining theorems have source citations, complete proof descriptions and
matching nodes. Small cases checked mathematically: degree zero uses the unit
basis; degree one is precisely the first-chart hypothesis; degree two is one
application of the normalized signed product. On the empty scheme the section
modules are zero and the sheaf maps unique. The extensionality statement allows
an arbitrary target and noninvertible maps; transporting along the realization
equivalence gives linearity over the constant coefficient sheaf. Thus it does not
mistake linearity over constant scalar elements for spanning by those scalars on
an arbitrary disconnected site object.

## No longer needed

None. No existing import, node, module, declaration or unit step was removed or
withdrawn. The original node had no numbered proof plan or proof dependencies;
the new argument expands its existing docstring using the stated signed products.
The existing public imports are retained to preserve the public interface.

## Where the brief, the DAG or earlier work was wrong

The initial shared source had two holes, but refreshed during the first reading:
U5's first-chart proof appeared before the module was copied into the sandbox.
The copied baseline therefore has only the positive-family hole. Its node's
`proof` and `proof_deps` were empty; the proof in words was in its Lean docstring.

Searches found generic fully faithful lifting, basis extensionality and sheaf
extensionality results, but no declaration supplying the ordered-frame section
normalization or compatible-frame test needed here. The new statements preserve
all hypotheses and conclusions of the item and separate these missing steps.

## New nodes

`lem-pur-finite-positive-chart-recursion` records normalization of the explicit
ordinary tensor recursion in `Sheaf.Paper.FinitePositiveChartRecursion`, including
the constructed zero chart and positive chart family. It asserts only the forward
basis computation for that construction, rather than existence and uniqueness.

`lem-pur-finite-positive-chart-frame-ext` records extensionality of maps from one
positive line to an arbitrary coefficient sheaf, in
`Sheaf.Paper.FinitePositiveChartFrameExt`. It supplies only the uniqueness step;
it constructs no chart or family. No change record is needed because no existing
statement or definition is changed.

Validation: the required `lcompile.py --all` compiled all three delivered modules
successfully, with no compiler diagnostics. Each Lean line is at most 100 columns.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
