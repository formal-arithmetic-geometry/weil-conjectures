## What changed

Repair of return C-87af9 (head `87af93ea0a3`): removed the inherited
`set_option warn.sorry false` command. The landing ledger recognized its
option-name suffix as an unattributed hole at line 32, offset 1380.
No mathematical declaration or proof changed in this repair. Compared the
retained packet with current shared source: the original module and node
metadata still agree outside the previously reviewed packet changes.
The delivery tool rebuilds this packet on freshly fetched `sheaf-dag`.
The source-ledger scanner now attributes exactly two holes to the two named
intermediate theorems, with no warnings. Server compilation of all four modules
passed after the repair.

Replaced the hole in `WeilConjectures.purReductionLimitShiftAdjunction` by a complete
assembly of the unchanged `PurReductionLimitShiftData` fields. The right shift is
`SequenceKInjectiveComparison.totalLimitCommShift`; the left shift is the actual
adjunction's canonical mate. The right-limit normalization obligation includes
the prescribed replacement-model equation, using the existing proved generic
`comparisonIso_shifts` as its first step.
Mathlib's adjunction shift identities supply the unit and counit equations.
Local irreducibility prevents expansion of the large coefficient constructions;
unneeded auxiliary size-of/injectivity generation is disabled in the data module.
The limit model is normalized to the existing `comparisonIso` construction,
which is the same canonical composite by `Functor.mapIso_trans` and
`Iso.trans_assoc`. Every explicit signature stays unchanged.

Two new theorem modules isolate finite-model normalization and signed normalized
Roos triangles. The five existing helper/data declarations move to
`Sheaf.Paper.PurReductionLimitShiftData`, publicly re-exported by the item, to avoid
import cycles. Definition-node ownership follows that move. The limit-model body is normalized
to the already proved comparison API to prevent expensive conversion during checking. There are no consumer
adaptations and no changes under `lean/WeilConjectures`.

## Proved and sorry left

Original hole: `WeilConjectures.purReductionLimitShiftAdjunction` (one). Its body is
now complete from the two lower obligations and the already proved library results.
The replacement-model specialization was attempted using the proved generic
lemma, but conversion across the old large coefficient constructions exceeded
the file time limit. It is explicitly included in the right-limit normalization
obligation; no claim is made that this specialization is proved in the packet.

Added holes (two), each a public theorem with body exactly `by sorry`:

- `WeilConjectures.purReductionFiniteShiftNormalization`, node
  `lem-pur-reduction-finite-shift-normalization`.
- `WeilConjectures.purCoefficientRoosShiftNormalization`, node
  `lem-pur-coefficient-roos-shift-normalization`.

The item has zero local holes; this packet has two holes. This is a decomposition
of one hole into two, not a net proof: one upper hole closed, two lower holes added.
The lower statements separately address only the finite-reduction clauses and the
right-limit resolution and Roos clauses. The product-existence, unit, counit and final
assembly work is real Lean in the item. No data definition contains a hole or
chooses an arbitrary witness from a holed existence statement.

## No longer needed

The item's old three-step route is replaced below its unit. It does not use
`lem-pur-sequence-adjoint-resolution-shifts` or
`lem-weil-pbc-derived-adjunction-shift`, nor import their modules. The existing
`lem-pur-injective-tower-roos-shifts` remains needed by the new Roos obligation;
it is not pruned. The generic proved replacement-shift helper in
`Sheaf.Paper.SequenceKInjectiveComparisonShifts` is the stated starting point for the new right-limit obligation, rather than its
geometrically restricted final theorem.

Removed proof imports from the item:

- `Sheaf.Paper.DerivedAdjunctionShift`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`.
- `WeilConjectures.Algebra.Homology.RoosSplitComparison`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.

The corresponding obsolete top-level tool approvals are removed from the parent
node: `lem-pc-ringed-space-product-kinjective`,
`lem-weil-pbc-derived-adjunction-shift`,
`lem-weil-pbc-exact-functor-derived-functor`, `lem-weil-pbc-kinjective-shift`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, `lem-weil-roos-split-comparison`,
`lem-weil-tower-category-levelwise-abelian`, `lem-weil-tower-evaluation-kinjective`.
Some remain transitive tools of the new obligations; no declaration or module is
withdrawn and no claim is made that their other consumers no longer need them.
All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The planned sequence-adjoint theorem requires a finite-field datum, l different
from its characteristic, and finite-type/quasicompact structure on W. The item's
unchanged Lean statement has none of these hypotheses. Its geometrically generic
cochain argument is needed here. The proved sequence-K-injective module already
contains the general replacement-shift lemma. Its specialization has a large
conversion cost under the current coefficient definitions, recorded above.

The existing proved injective-tower Roos theorem requires injective terms, whereas
the item accepts every K-injective tower. The new Roos obligation explicitly
includes homotopy-equivalence transport and independence from that replacement.
Neither mismatch authorizes changing the item's signature. The unit's statement
and recorded route remain intact. A source-only graph walk found no path from
these dependencies back to the item, in both baseline and packet. Cycles found
farther down the shared DAG predate this packet and are outside this assignment.

## New nodes

`lem-pur-reduction-finite-shift-normalization` fixes the reduction shift to the mate
of the canonical limit shift and asserts only finite K-flat normalization plus
evaluation compatibility. It does not assert products, resolution-model squares,
Roos triangles or unit/counit clauses. Its proof in words derives tensor shifts and
uses uniqueness of adjoint mates. Its edge cases include zero and negative shifts,
zero complexes and the empty scheme.

`lem-pur-coefficient-roos-shift-normalization` concerns only total limit and Roos
triangles for supplied K-injective models. It extends the existing signed
injective-term theorem through tower homotopy equivalences, preserving actual
projections and all shifted choices. It also includes the canonical replacement-model shift square needed to identify
the transported right shift. It asserts no reduction or adjunction data.
Its signed zero, ±1 and repeated-shift checks are recorded in the docstring/node.

Change record: `coord/changes/pur-reduction-limit-shift-data-module.md` lists the
moved definitions and the limit-model normalization and all fourteen downstream consumers with snapshot
holders. Their statements and meanings are unchanged by the public re-export.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
