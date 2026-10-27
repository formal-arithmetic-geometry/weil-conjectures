## What changed

Replaced the hole in `WeilConjectures.purSequenceProjectionHomNormalization` by a
complete assembly proof. It constructs the resolution-data record from ordinary
and derived pieces, proves the whole-Hom formula by the unit equation and
naturality, and proves the simultaneous-replacement formula by cancellation,
ordinary-transpose normalization and the composition-model equation.

Added `Sheaf.Paper.PurSequenceOrdinaryFactorization`, isolating the geometric
projection, ordinary adjunction and constant-ring factorization (original steps
1–2). Added `Sheaf.Paper.PurSequenceComparisonTranspose`, isolating the chain-map
compatibility of the two universal coefficient comparisons (original steps 3–7).
Added `Sheaf.Paper.PurSequenceDerivedNormalization`, which assembles every field
of the derived-data record from that compatibility and the existing universal
K-flat and K-injective comparison declarations. The derived functors and
adjunction in this assembly are precisely those of the supplied calculus;
its two comparison isomorphisms are identities.

No existing signature, definition, public import, target or consumer changed.
The new results quantify over independent scheme and coefficient universes.
The derived-data record is constructed explicitly in the proof, without choosing
arbitrary data from an unproved existence statement in a definition.

## Proved and sorry left

Closed the original hole:
- `WeilConjectures.purSequenceProjectionHomNormalization`
  (`lem-pur-sequence-projection-hom-normalization`).

Proved the new assembly theorem:
- `WeilConjectures.purSequenceDerivedNormalization`
  (`lem-pur-sequence-derived-normalization`), from the existing K-injective
  comparison and the new comparison-transpose theorem. Every record field has
  a proof, including the universal properties and prescribed replacement iso.

Two new holes remain, each in its own public theorem, module and DAG node:
- `WeilConjectures.purSequenceOrdinaryFactorization`
  (`lem-pur-sequence-ordinary-factorization`): the ordinary geometry and
  factorization, independent of the supplied calculus and all derived inputs.
- `WeilConjectures.purSequenceComparisonTranspose`
  (`lem-pur-sequence-comparison-transpose`): a compatible left comparison and
  its chain-map transpose equation, for an already supplied ordinary
  factorization and normalized right comparison.

This is a decomposition: one original hole closed and two lower holes added,
net minus one in the delivered declarations. It is not a net proof of the
mathematical item. The original whole-Hom and simultaneous-replacement clauses
are proved by actual Lean compositions rather than restated under new names.
Existing imported K-flat and K-injective comparison holes remain in their
original modules and are not claimed as closed.

## No longer needed

The item itself now needs only the two construction modules and its unchanged
public data import. Its old private imports were removed:
- `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`
- `Sheaf.CategoryTheory.SequencePushforwardLimitProjections`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`

These are removed as direct dependencies of the item; they are NOT globally
withdrawn. The ordinary and transpose subarguments still require the generic
sequence adjunction, K-flat resolutions, resolving adjunction, K-injective
resolutions and composition arguments recorded in their nodes. Consequently
no library module or mathematical lemma is claimed globally unnecessary.
The original top-level tool-use approvals were removed from the item's node
because the actual assembly calls the construction lemmas instead. Their
mathematics stays in the corresponding lower-node proof plans.

## Where the brief, the DAG or earlier work was wrong

The original node supplies a valid informal seven-step plan but no existing
Lean declaration directly inhabits its large resolution-data record. A generic
sequence-site theorem does not directly provide its coefficient-specific
ordinary comparisons or constant-ring factorization. In particular the generic
`pushforwardLimitProjections` conclusion does not itself identify the supplied
calculus adjunction by an equality on whole Hom sets. This final compatibility
is isolated in the comparison-transpose node; it is not inferred from evaluated
Hom sets or from faithfulness of evaluation.

The parent `purSequenceAdjointResolutionShifts` would trivially supply the
record, but its DAG depends on this item. It was deliberately not used. The
existing K-flat and K-injective comparison siblings have no DAG path back to
this item and can be used independently.

Edge cases checked in formulating the new statements: empty W; zero complex;
identity replacement; arbitrary unbounded complexes; nonsurjective quotient
tower transitions; nonflat coefficient maps; and restriction of a K-injective
system not being K-injective. The ordinary result adds no finite-type
hypothesis. The transpose statement chooses a compatible left comparison,
rather than incorrectly claiming the equation for an arbitrary left comparison.

## New nodes

`lem-pur-sequence-ordinary-factorization` contains original steps 1–2 with the
constant-ring factorization, exact scalar restriction, and actual ordinary
coordinate transposes. It is a proper part of the argument and has no derived
calculus or Hom statement.

`lem-pur-sequence-comparison-transpose` contains the compatibility step for the
two canonical universal comparisons. It assumes the ordinary factorization and
an already normalized right comparison, and produces only a compatible K-flat
comparison with a chain-map equation. It has no whole-Hom conclusion and
constructs neither the geometry nor the simultaneous-replacement record.

`lem-pur-sequence-derived-normalization` is proved. It assembles the record from
the existing K-injective comparison and the new transpose result. Its Lean
proof transports the left Kan universal property, reuses the explicit canonical
replacement iso and prefixes the existing lim(j) equation by the ordinary
limit identification.

No definition or statement change records were needed.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
