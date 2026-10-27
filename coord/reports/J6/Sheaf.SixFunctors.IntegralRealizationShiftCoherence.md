## What changed

Filled `integralRealizationShiftCoherence` by conditional tree transport from the supplied
insertion and recursion theorems. All original public declarations, signatures, definitions,
and public imports are unchanged. New private proofs preserve labelled occurrence sets,
propagate injectivity through canonical compositions, convert synchronized pairs to the
selected tree relation, derive generator intertwining from `R.coherence`, and apply total
limit to the intrinsic system square through a generic functor/naturality lemma.

Two new modules isolate smaller remaining obligations: the intrinsic square for one basic
system generator, and existence of a synchronized reevaluation after shifting one input.
The original item contains no `sorry`; its proof combines these distinct steps with the
existing conditional tree theorem. This is a decomposition, not a claim of an axiom-free
proof of the target.

Validation: both new modules compiled with `lcompile.py --all`; the final assigned
module compiled cleanly with `lcompile.py` in 12.8 seconds, without development options.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralRealizationShiftCoherence`
(node `lem-pur-integral-realization-shift-coherence`) by reduction.

Added exactly two holes, each in a public named theorem with a complete proof in words:

- `WeilConjectures.IntegralSystemRealization.canonicalTreeGeneratorSystemShift`,
  node `lem-pur-canonical-tree-generator-shift-laws`: only the intrinsic system square
  for one synchronized basic constructor, before total limit or expression-context closure.
- `WeilConjectures.IntegralSystemRealization.canonicalShiftSynchronization`,
  node `lem-pur-canonical-shift-synchronization`: only existence of the reevaluated
  synchronized construction, with no system or integral shift equation.

Actual counts: original item 1 to 0 holes; added modules 2 holes; total packet 2 holes.
One upper hole closed and two strictly smaller obligations added: net -1, a decomposition.
The private helper proofs and the full assembly have no admitted steps. A local
irreducibility attribute for `HasDerivedCategory.standard` controls elaboration only;
it exports no interface change. The concrete limit helper uses an explicit shift
isomorphism and locally respects transparency, avoiding expansion of the derived-category
model. Temporary profiling options and diagnostic commands have been removed.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`
- `Sheaf.Paper.DerivedAdjunctionShift`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.PurReductionLimitShiftAdjunction`
- `Sheaf.SixFunctors.GeneratorReductionStatement`
- `Sheaf.SixFunctors.IntegralBasicOperationShift`
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`
- `Sheaf.SixFunctors.OpenAdjunctionShift`
- `Sheaf.SixFunctors.SystemPrimitiveComparisonShift`

Retained the recursion import because the proof uses its equations. The direct proof now
uses the insertion theorem, recursive equations, conditional tree
transport, the local generator-square obligation, and synchronization existence. The
system-adjunction/open and proper/open/projection nodes remain necessary below the new
local-generator node; their arguments are not discarded. The compact-support strict-Roos
model theorem is not needed for this assembly: the public claim is about the already fixed
operation comparisons, and the conditional tree theorem includes the recorded compact-support
open/proper composite. The stronger theorem about explicit tower transitions and representative
normalization remains available for its own consumers. No module is withdrawn and no global
unreachability is asserted.

The existence theorem `lem-sf-integral-compactification-system-realization` is not invoked:
`R` is supplied as an argument, and its completion and coherence fields supply the actual
intertwining. Its definition node remains necessary. Removed the stale direct `tool_uses`
approvals for `lem-weil-pbc-commshift-nattrans-comp-whisker`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-weil-pbc-derived-adjunction-shift`, `def-exchange-projection`, and
`lem-sf-compact-support-restriction-of-scalars`; none is directly invoked by the assembly.

## Where the brief, the DAG or earlier work was wrong

The DAG's short assembly omits two interfaces in the current declarations: matching the
published one-slot system-generator APIs to `TreeGeneratorShiftLaws`, and constructing
synchronized maps at different input families. `SynchronizedPair.diagonal` supplies only the
same family twice. The tree theorem is conditional and asserts squares only for its selected
synchronized subrelation; it does not supply shifted maps. Moreover that subrelation requires
injectivity of every intermediate composition expression, whereas `SynchronizedPair.comp`
does not store it. The packet proves preservation of labelled occurrence sets and hence that
injectivity, rather than adding an assumption to the original theorem.

The conditional proper/open-pasting API also requires explicit bounds on additional
internal systems, and its exchange constructor requires a cartesian square. Neither
condition is supplied for every `SynchronizedBasic.exchange`. The local-generator
obligation therefore records the direct global mate/pasting calculation for those
cases; its proof does not assert that endpoint domains imply those extra tests.

The two new statements were checked on zero shifts, negative shifts, absent labels in
subexpressions, both tensor slots, repeated object values with distinct labels, identity
maps, and empty opens. The unit route and target statements are unchanged.

## New nodes

`lem-pur-canonical-tree-generator-shift-laws` records the remaining intrinsic system equation
for a basic constructor; it deliberately omits integral intertwining, which this packet proves
from the supplied realization record. Its proof plan uses the existing primitive and
adjunction/open declarations and the explicit mate/pasting formulas, handling general
commutative exchange squares directly. Mathlib searches returned only generic shift APIs
and unrelated declarations, not this constructor-identification statement.

`lem-pur-canonical-shift-synchronization` records the structural existence induction with
shifted completion inverses and intermediate admissibility. Its proof is independent of the
shift-square calculations. Searches found the existing components and diagonal APIs, which
are insufficient for different input families. Both new nodes retain the current blueprint
provenance and the item's chapter and unit. No shared interface or change record is needed.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
