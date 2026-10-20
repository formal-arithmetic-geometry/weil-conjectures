# SemilinearDerivedSections proof scopes

## Reason

The main proof needs private lemmas about evaluated adjunction transposes, reduction
naturality and normalized geometric projection. These are proved after the existing
categorical evaluation section, and the existing existence theorem is placed after them.
This adds a namespace reopening and repeats the original variable context. Preflight
classifies the changed command layout as a visibility change and requires this record.
There is no change to any existing public signature, definition body, public import,
instance, notation, or attribute. All added helper declarations are private theorems.

## Old

```lean
end CategoricalEvaluation
end WeilConjectures.SemilinearSections
```

The existing `semilinearDerivedSections` theorem was earlier in the file, with its
original variable context, and had proof `by sorry`.

## New

```lean
end CategoricalEvaluation
end WeilConjectures.SemilinearSections

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
```

The private proofs and the unchanged statement of `semilinearDerivedSections` follow
in this identical variable context. Local `set_option ... in` commands affect only
the private proofs' elaboration. All scopes close at the end of the module.

## Users

`tools/downstream.py Sheaf.Paper.SemilinearDerivedSections --uses
semilinearDerivedSections` reports the following direct declaration consumers. No
consumer needs adaptation because every existing signature and definition is identical.
The transitive import closure is likewise unaffected by private proof scopes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearDerivedSections | E8 | private proof scopes; same public signatures |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unchanged; no adaptation | none |
| Sheaf.Paper.FiniteFreeCompactComposition | unchanged; no adaptation | none |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unchanged; no adaptation | none |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unchanged; no adaptation | none |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | unchanged; no adaptation | none |

No module held by another group is modified, and no target definition or statement is
changed. No forced adaptations are part of this delivery.

## Status

landed 20261020T051225-L-1599989 2026-10-20 (merge of deliver/E8/Sheaf.Paper.SemilinearDerivedSections)
