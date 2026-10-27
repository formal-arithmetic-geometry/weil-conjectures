## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSheetSum_compatible`
in `Sheaf.Paper.FiniteEtaleSheetSumCompatibility`, preserving its statement and the
existing sum definition. All added helpers are private and proved. Added private
proof imports of `Mathlib.Tactic.CongrExclamation`,
`Sheaf.Paper.ProfinitePointPullback`,
`WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent`.

The proof constructs the base-changed coproduct presentations, applies the existing
local permutation theorem, transports each counit projection by inverse-image
coherence and naturality, and reindexes the sum on each open neighbourhood.
Faithful forgetting and the existing open-restriction extensionality theorem
then descend equality. The sum calculation is first proved for an arbitrary
morphism between pullbacks, keeping the large concrete counit out of repeated
kernel conversions; a local irreducible wrapper has exactly the actual counit as
its body. A local congruence calculation compares cast arguments syntactically and proves
their equality explicitly, using heterogeneous congruence and proof irrelevance.
This avoids expensive kernel conversions between the imported equality casts
and their locally constructed counterparts. Chart sums also have
private irreducible wrappers with explicit morphism types. Empty sheet lists and
empty bases require no exceptions.

Updated the item's DAG proof, proof dependencies, and proof origin to describe
this argument. All shared definitions are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSheetSum_compatible`
(`lem-sfb-finite-etale-sheet-sum-compatible`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
No statement or definition was weakened or replaced.

Validation: the complete module compiled in 12.1 seconds without warnings.
`#print axioms finiteEtaleSheetSum_compatible` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`; the diagnostic command was removed.

## No longer needed

Removed the proof-dependency edge to `lem-pur-sheaf-hom-cover-gluing`
(`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`): this item only
needs detection of equality on an open cover, supplied by the existing
`ProEtale.hom_ext_of_openImmersionRestriction`. It does not construct a glued map.
This is pruning of this item's proof edge, not withdrawal of that shared module.
The dependency on `lem-weil-proetale-weakly-etale-localization`
(`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`) is replaced by the
already proved source-library inverse-image/restriction comparison, corresponding
to `lem-sfb-proetale-object-inverse-image-restriction`. No existing import was
removed. The public import of
`Sheaf.Paper.FiniteEtaleSplitHomDescent` remains necessary for `Compatible`.

The planned identification of counit projections with separate local-coordinate
restrictions, and its adjunction-triangle calculation, is unnecessary: naturality
of `upperStarComp` works directly for the actual counit, without assumptions on p.
The localization comparison is still used to detect equality on the open cover.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's local permutation route works, but its
proposed gluing step was stronger than necessary. The actual argument uses only
open-cover separatedness and the existing normalized module pullback comparisons.
The theorem needs no additional finiteness, etaleness, nonempty-base or
positive-degree assumptions. The fixed unit route is preserved.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
