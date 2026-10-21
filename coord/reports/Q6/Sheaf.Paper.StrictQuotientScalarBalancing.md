## What changed

The original theorem keeps its exact signature. Its scalar balancing comes from
`ConstantCompletion.derivedReductionTowerComparison`. The augmentation is the universal
left-derived lift of `reductionUnit`. Exact localization supplies constant-diagram
restriction. A categorical cancellation proof combines these normalized computations;
the strict ordinary unit formula is proved on sections, and flat K-flat resolutions
extend the augmentation equation to all derived objects.

The original concrete definitions are moved verbatim to
`Sheaf.Paper.StrictQuotientScalarBalancingData`, publicly imported by the original module.
This avoids a cycle with the new pullback-only result. A mechanical comparison verifies
that the moved declaration blocks are byte-identical after changing only blueprint tags.
The change record is `coord/changes/strict-quotient-scalar-balancing-data-Q6.md`.

Validation: the data module compiled cleanly in 16.9 seconds and the final main proof
compiled cleanly in 22.2 seconds through the prescribed remote `lcompile.py` tool.
Delivery additionally compiles all three modules together and runs its preflight.

The independently meaningful pullback argument (original steps 4--7) is stated in
`Sheaf.Paper.StrictQuotientPullbackCompatibility`. It fixes the prescribed ordinary and
derived maps, not only their existence as unrelated isomorphisms. The root theorem
assembles that result with the proved augmentation argument.

## Proved and sorry left

Closed in the item:
`AlgebraicGeometry.Scheme.StrictScalarBalancing.strictQuotientScalarBalancing`.
There are zero literal `sorry` in the item or the data module.

Added and still unproved:
`AlgebraicGeometry.Scheme.StrictScalarBalancing.strictQuotientPullbackCompatibility`,
node `lem-weil-pbc-strict-quotient-pullback-compatibility` (one `sorry`).
It is strictly the pullback part of the original argument, with no augmentation
assertion. The nontrivial augmentation equation is proved in Lean, not assumed by
this new lemma. This delivery is a decomposition: one hole closed and one added,
net zero, rather than a claim that the entire dependency closure is proved.
The original dependency `ConstantCompletion.derivedReductionTowerComparison` remains
unproved in its own existing module; it is not a hole added by this delivery.

## No longer needed

Removed the following direct proof imports from the original file and did not copy
them into the data module:
`Mathlib.Algebra.Homology.BifunctorShift`,
`Mathlib.CategoryTheory.Abelian.FunctorCategory`,
`Sheaf.CategoryTheory.FiniteTypeConstantExact`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.Paper.RingedTopoiInverseImageTensorComparison`,
`Sheaf.Paper.RingedTopoiTensorSections`,
`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
and (reviewer) `Sheaf.Paper.FlatCommonQuotientReductionTower`.
The obsolete `tool_uses` entries for `lem-pur-derived-change-of-rings` and
`lem-pe-constant-left-module-inverse-image` are removed from the root node;
the derived-change-of-rings tool remains part of the new pullback argument.
The constant-left-module inverse-image node is unnecessary there too: the given
natural isomorphism `inverseData.constants` already identifies the constant rings.
The existing K-flat-resolution tool approval is retained in its original order.

The root proof directly reuses the more specific existing normalized quotient
comparison rather than reconstructing its common-quotient tensor argument.

All original public imports are retained verbatim in the original module and in the
data module. The plain import of `Sheaf.Paper.FlatCommonQuotientReductionTower` is no
longer needed either (reviewer correction): the root proof uses no declaration of it,
and the integral-models unit route realizes that node through its own importers
(RingedCommonQuotientPullbackComparison, PulledReductionStrictTowerComparison,
DerivedFiniteQuotientCoherence), not through this module. The new pullback
node keeps the profinite-coefficient, tensor-pullback and tensor-descent dependencies
of original steps 4--7. It records explicitly the flat-restriction and levelwise
computations which those steps referred back to in original steps 1--2. The general
constant-left-module comparison is replaced by the given constant-ring isomorphism.
No old module or node is claimed globally pruned. The diagram-site, profinite-coefficient
and tensor-descent nodes still belong to the pullback argument.
Two new direct consumers, `Sheaf.Paper.QuotientDiagramScalarProjection` and
`Sheaf.Paper.CompletedScalarUnitAdjunction`, were published during this session.
They use the unchanged public definitions; every original public import is retained
and no consumer adaptation is necessary. Both are listed explicitly in the change record. The root theorem keeps its exact original signature.

The remaining pullback proof uses the general K-flat-resolution and derived-change-of-rings
tools to compute quotient tensor on a common representative, including a resolution of the
quotient factor. The proper-base-change unit does not replace this general resolving-class
theory. These tool uses are reported for the maintainer; no new tool approval is written.

The unit route is preserved; no unit, parent node or source-library declaration is
withdrawn or bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing
`ConstantCompletion.pullbackTowerComparison_existsUnique` gives a comparison after
restriction to constant coefficients. It does not directly provide the
completed-coefficient comparison required by `PullCompatibility.ordinaryCompleted`.
Similarly the chosen `InverseImageData` on the small sites is not definitionally the
original-site coefficient inverse image in the profinite theorem. Its bridge must
retain the projection and insertion normalizations. The new pullback result records
exactly that remaining mathematical work, with a full proof in words.

The existing shared dependency graph contains the cycle
`lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. The same cycle is present before and after
this packet; no new dependency cycle was introduced. Those unrelated nodes are unchanged.

The standard derived-category localization instance sometimes needs its explicit
`HasDerivedCategory.standard` presentation; the proof uses that presentation.

## New nodes

`def-weil-pbc-strict-quotient-scalar-balancing-data` owns the unchanged concrete
definitions extracted from the root. It adds no proof hole and no new mathematical
assumption.

`lem-weil-pbc-strict-quotient-pullback-compatibility` isolates the existing source
argument for canonical pullback/tensor reassociation and its scalar-balancing cube.
Its hypotheses require the two normalized scalar-balancing computations, and its
conclusion supplies only the pullback record. Edge cases include the zero ring,
unit and zero ideals, empty schemes and identity morphisms; the same insertion and
quotient formulas apply. This is neither a renamed copy of the root statement nor
an augmentation assumption.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
