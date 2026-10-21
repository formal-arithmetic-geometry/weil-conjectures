## What changed

Restored the previously reviewed proof packet for
`Sheaf.Paper.CoefficientSystemDerivedComparison`. The target theorem now obtains the
ordinary coefficient-system image and the two evaluation-derived packages, applies the
unbounded comparison construction, and proves the remaining detection, bounded-below,
essential-image counit, and normalization conclusions by explicit categorical lemmas.
The packet adds the generic image-data interface, ordinary system assembly, unbounded
comparison interface, and proved exact-derived descent lemmas. All delivered Lean files
compile with `lcompile.py --all`; the target statement is unchanged.
The representation extraction is recorded in
`coord/changes/B4-coefficient-system-image-interface.md`.

## Proved and sorry left

Closed the original hole
`SheafOfModules.coefficientSystemDerivedComparison` (one hole).

Two genuinely separate construction results remain as named sorries:

- `SheafOfModules.coefficientLevelOrdinaryImage_exists`, node
  `lem-pur-coefficient-level-ordinary-images`;
- `SheafOfModules.coefficientSystemUnboundedComparison`, node
  `lem-pur-coefficient-system-unbounded-comparison`.

No definition contains `sorry`. The generic descent lemmas and ordinary-system assembly
in the delivered packet are proved.

## No longer needed

The retained proof does not use the former direct K-injective, K-flat, tensor,
pre-derived-adjunction, pushforward-composition, bounded-below-resolution, or
negative-vanishing imports. Their direct proof approvals are removed from the copied
node; they remain available to other consumers. No source-library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original monolithic proof plan mixed the unbounded construction with the formal
descent argument. The construction requires two separate interfaces: normalized
ordinary coefficient lifts and the unbounded evaluation comparison. Factoring these
results makes the top-level proof a real combination of strictly smaller statements;
the target statement and all existing public signatures remain unchanged. The previous
reviewed packet for this item had already compiled and passed global verification before
being removed from a later batch, so its proof and node metadata are restored here.

## New nodes

- `def-pur-coefficient-system-image-data`: extracted image-data interface and generic
  derived comparison structures.
- `lem-pur-exact-derived-adjunction-bounds`: proved exact-derived bounds,
  conservativity, and essential-image counit lemmas.
- `lem-pur-scalar-adjunction-descent`: proved scalar mate descent.
- `lem-pur-coefficient-level-ordinary-images`: ordinary-level construction (sorry).
- `lem-pur-coefficient-system-ordinary-images`: proved ordinary system assembly.
- `lem-pur-coefficient-system-unbounded-comparison`: unbounded evaluation comparison
  (sorry).

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
