## What changed

Completed the proof of `AlgebraicGeometry.Scheme.etaleOriginProperOpenInterchange` without
changing its statement or its four claimed conclusions. A proved private categorical
`open_mate_transport` lemma transposes the five-arrow composite. The etale interchange's
recorded normalization and the general restriction-transport lemma identify that transpose
with intrinsic lambda inverse. The canonical counit formula is natural on every intrinsic
object; conjugating it by a witness proves independence and naturality without lifting maps
through site-comparison full faithfulness. The adjunction inverse identity proves the unit
normalization.

Added `Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport`. It contains the separate
general qcqs restriction-coherence obligation and two explicit composite definitions. To
avoid an import cycle, the four preexisting comparison definitions are relocated unchanged
into this module and publicly reexported from the parent. The parser comparison verifies
identical signatures and bodies for all four. Change record:
`coord/changes/F7-etale-origin-open-comparison-relocation.md`.

The original etale interchange choice is expressed through the existing definitionally
equal `Etale.properOpenCoefficientInterchange` wrapper. It selects exactly the same
isomorphism; the change record displays both bodies. Local irreducibility also keeps the
etale functors folded. The restored pair compiled in 8.9 seconds (restriction) and 26.8 seconds (main).
After an intermittent timeout during delivery, profiling located an expensive `change`
across the interchange-choice wrappers. The proof now unfolds the two wrappers explicitly
with `rw` before applying the recorded normalization, and compiled in 44.9 seconds.
This removes the expensive inference without splitting the file or changing the chosen map. A temporary
copy of the direct downstream consumer CompactSupportUniformTorBound compiled against the
sandbox in 37.5 seconds (the test copy is removed).

Single-module compilation is checked through lcompile; the final dry run performs the
node, consumer and independent-reader packet checks. All options preserve kernel checking;
local irreducibility keeps canonical realization/comparison definitions folded. The unit
record has no separately realized step to bypass; the retained proper/open route is kept.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.etaleOriginProperOpenInterchange`.
The private `AlgebraicGeometry.Scheme.open_mate_transport` is completely proved.

Added one hole:
`AlgebraicGeometry.Scheme.etaleOriginOpenRestriction_transport`, node
`lem-exc-etale-origin-open-restriction-transport`. Its proof is exactly `by sorry`.
There are zero holes in definitions and zero remaining holes in the item module.
This is a decomposition: one original hole closed, one separate lower hole added, net zero.
The retained theorem asserts only transport of a restriction square for an arbitrary qcqs
map and open immersion, without properness, Noetherian assumptions, any proper/open
interchange map, witnesses, independence or naturality conclusions. It is strictly the
restriction calculation in the source argument, not the item restated.

The missing Lean calculation is the derived sectionwise restriction square through the
fixed-scalar-to-intrinsic realization, including D+ inclusion isomorphisms. The existing
transport-identifies-exchange theorem gives the fixed-scalar exchange square but not this
intrinsic restriction/unit equation directly. I checked its full signature, the unit
normalization theorem, and the canonical direct-image comparisons. The new node records
how to derive that remaining square on K-injectives, then cancel the two open units. Its
hypotheses were checked on identity maps/opens, empty opens, zero objects and the zero ring;
all yield the same identity or zero-map square. No arbitrary data is chosen from existence.

## No longer needed

The full-faithfulness proof dependency `thm-weil-pbc-site-comparison` is unused: once the
canonical counit formula is established, naturality identifies all conjugated witnesses.
`Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness` is removed as a direct proof import.
This does not assert those modules disappear from every other target's closure.

Removed direct proof imports (the restriction lemma retains the dependencies its own
statement or proof uses):

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.CondensedAmbientExchange`
- `Sheaf.Paper.PbcActualRingedExchange`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`

Removed redundant direct public imports; their required declarations remain publicly
available through the new restriction module and its public imports:

- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.Paper.RingedEtaleOriginWitness`
- `Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`

Pruned original proof-only nodes from the parent's direct proof dependency list:
`def-weil-closed-immersion`, `def-weil-finite-type-morphism`,
`def-weil-pbc-ambient-ringed-exchange`, `def-weil-pbc-derived-categories`,
`def-weil-pbc-etale-origin-witness`, `def-weil-proper-morphism`,
`lem-weil-extension-by-zero-exact`, `lem-weil-pbc-extension-by-zero-exact`,
`thm-weil-pbc-site-comparison`.
Comparison pullback, exchange transport, exact unbounded exchange and open-unit
normalization remain dependencies of the new restriction node; they have not been pruned
from the argument. In particular no claim of global pruning is made for these dependencies.
The original `tool_uses` list is only pruned, with relative order retained: removed
`thm-weil-pbc-site-comparison` and `def-weil-pbc-ambient-ringed-exchange`.
The new module also omits the unused proof imports OpenComparisonUnitNormalization,
SupportComparisonPullbackCoherence and SmoothBaseChange: its named remaining theorem has
no partial proof using them. Their nodes remain in its proof plan. Redundant compatibility
imports AB, OpenImmersionLowerShriekCoherence and UpperLowerStar.CoherenceLegacy are not
needed in the new module; the parent still reexports them via ProperOpenCoefficientMate.
The wrapper is retained after a fresh trial of the expanded original choice with these
three compatibility imports again timed out. Its broader transitive imports are a cost
of this implementation; the removals above describe direct dependencies, not a claim
that the whole import closure shrinks.
Local irreducibility attributes in the new module keep comparisons folded in its later
explicit composites. With the minimal imports the new module compiles in 7.3 seconds.

## Where the brief, the DAG or earlier work was wrong

The original witness-independence plan unnecessarily lifted transitions through full
faithfulness. Equality to the canonical natural counit formula proves more directly the
required independence and naturality for arbitrary ambient morphisms.

The original plan's sectionwise-to-derived intrinsic restriction calculation is a genuine
coherence obligation, not a direct application of the fixed-scalar exchange theorem as
currently stated. It is now isolated with its exact equation, complete natural-language
argument and source. No statement is disputed and no target or original theorem signature
is changed. Searches of the DAG and blueprint found no existing node stating that equation;
Mathlib searches (LeanSearch, LeanFinder/Loogle and grep) found generic adjunction identities
or structure-sheaf restrictions, not this fixed-coefficient small-site result.

Provider interruptions also reset the sandbox reference clock: the earlier saved start was
1792426307.0062191 and the resumed metadata reads 1792437810.4975526. I did not edit `.budget`
or dispatcher files; useful proof and packet work continued. Logs under scratchpad preserve
the compile attempts (`restore-context`, `prune-final`, `merged-comparisons`, `no-wrapper`).
The resumed dry run was killed by the host with exit code 137 before producing output;
no push occurred. It is retried after checking that the process ended.

## New nodes

`lem-exc-etale-origin-open-restriction-transport` is the general comparison transport of
normalized open restriction. The node attaches its single theorem and the explicit
comparison constructions in the new module. The four moved comparison definitions retain
their old implementations and names. Its source is the retained Step 7 restriction and
mate-pasting calculation (current blueprint Step 8), with Stacks 099R, 09AF and 09BN as the
comparison/open-restriction sources. The main node's proof and proof dependencies now match
the categorical combination written in Lean. The change record is
`coord/changes/F7-etale-origin-open-comparison-relocation.md`.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
