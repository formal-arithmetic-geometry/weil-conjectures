# CategoryTheory.ringCechTailTerm

## Reason

Move this abbreviation into Sheaf.Paper.RingCechConeLinearEquiv so that both the
explicit coordinate equivalence and its differential computation can use it without
an import cycle. The original module publicly imports that module. The abbreviation's
name, universes, signature and body are identical, and the original theorem signature
is byte-for-byte unchanged. This is a relocation, not a change of mathematical meaning.
All former public Mathlib imports remain available through the new public import.

## Old

In lean/Sheaf/Paper/RingCechAlgebraicConeCoordinates.lean:

```lean
abbrev ringCechTailTerm (A : CommRingCat.{u}) (r : ℕ) (g : Fin r → A) :
    ℕ → ModuleCat.{u} A
  | 0 => ModuleCat.of A A
  | q + 1 => ModuleCat.of A
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, g (t i)))
```

## New

In lean/Sheaf/Paper/RingCechConeLinearEquiv.lean, publicly imported by the original module:

```lean
abbrev ringCechTailTerm (A : CommRingCat.{u}) (r : ℕ) (g : Fin r → A) :
    ℕ → ModuleCat.{u} A
  | 0 => ModuleCat.of A A
  | q + 1 => ModuleCat.of A
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, g (t i)))
```

## Users

The downstream scan found two modules mentioning this name. There are no signature or
reducibility changes. No other existing module is delivered or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingCechAlgebraicConeCoordinates | R3 | Publicly imports the relocated abbreviation; statement unchanged. |
| Sheaf.Paper.RingCechCoordinateTensorStep | No current holder recorded locally; not adapted | Original source compiles against this delivery in 43.9 s; no change required. |

## Status

landed 20261026T121118-L-2751194 2026-10-26 (merge of deliver/R3/Sheaf.Paper.RingCechAlgebraicConeCoordinates)
