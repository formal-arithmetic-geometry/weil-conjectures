# WeilConjectures.ConstructibleTensorHom coefficient-category elaboration

## Reason

Restore the quarantined `Sheaf.Paper.TensorHomExchange` module from the path
in `coord/rework.tsv`. The archived module took 344 seconds in the global build,
despite three declaration-local heartbeat increases. Diagnostic elaboration
repeatedly unfolded the chosen coefficient valuation ring and concrete coefficient
categories while solving universe and instance constraints. Supply the known
site universes explicitly and use the inherited inclusion shift structure directly.

## Old

The full baseline is `quarantine/Sheaf/Paper/TensorHomExchange.lean`.
Its initial options include, verbatim:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The inclusion instance is:

```lean
instance inclusionCommShift (T : Scheme.{u}) (s : RingStage.{u} l) :
    (s.inclusion l Ω T).CommShift ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
```

`IntegralLift.shift_normalization` supplies its inclusion shift instance by the
last `inferInstance` in:

```lean
    (sfIntegralConstructible l E.carrier Y).ι inferInstance inferInstance inferInstance
```

Uses of the two-universe coefficient interfaces omit universe arguments, for
example `C l Ω X s`, `Operation l Ω X Y (s.stage l)`, and `s.inclusion l Ω X`.
The final theorem is:

```lean
theorem exists_family :
    ∃ R : System l Ω D hl (f := f), ∀ c : Compactification f,
      Nonempty (Family l Ω D hl f R c) := by
  sorry
```

`RationalDescent`, `rationalDirectChange`, and `Family` have a scoped
`set_option maxHeartbeats 1600000 in`, with a comment recording the timeout.

## New

Respect transparency in term and type unification. Keep the chosen valuation
ring folded, locally to this file:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Padic.coefficientExtensionIntegers
```

Supply `.{u, u}` to the existing two-universe interfaces: `C`, `Operation`,
`LeftRealization`, `Scalar`, `Comparison`, `FieldComparison`, `System`,
`RingStage.inclusion`, `rationalization`, `rationalScalar`, `commonInclusion`,
and `commonField`. Both the schemes and Ω already have universe `u`; these
annotations determine elaboration rather than add or remove universe parameters.
No category, object, map, normalization equation, or quantified hypothesis changes.
The final theorem now explicitly writes `System.{u, u}`.

The inclusion instance uses the same Mathlib construction directly:

```lean
instance inclusionCommShift (T : Scheme.{u}) (s : RingStage.{u} l) :
    (s.inclusion.{u, u} l Ω T).CommShift ℤ :=
  match s with
  | .finite E n => ObjectProperty.commShiftι (finiteTorConstructible l E.carrier n n.pos T) (A := ℤ)
  | .integral E => ObjectProperty.commShiftι (finiteTorConstructibleIntegral l E.carrier T) (A := ℤ)
```

In `IntegralLift.shift_normalization` the last instance argument is explicitly
`ObjectProperty.commShiftι (sfIntegralConstructible l E.carrier Y) (A := ℤ)`.
This is the inherited shift on the same
full subcategory, not a new shift structure. Remove the three elevated heartbeat
limits and their associated comments; the normal heartbeat and 60-second file
limits apply. Preserve every import, archived declaration and theorem proof body.
No new declaration or theorem hole is introduced. All local attributes disappear
at the end of this module and do not alter consumer elaboration.

## Users

`python3 tools/downstream.py Sheaf.Paper.TensorHomExchange --allow-missing
--uses RationalDescent rationalDirectChange Family` reports zero downstream
modules. A search of `lean/` and `quarantine/` finds no external import or use of
this namespace. No consumer adaptation is needed. The DAG attachment, all parent
references, the proof dependencies and the unit route are retained. Absence of
current Lean importers is not used to withdraw any mathematics.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TensorHomExchange | K6 | Restore the complete interface with explicit elaboration information. |

The final source compiled via `lcompile.py` in 31.4 seconds with no elevated
heartbeat limit. The archive and repaired file both have 36 declarations and
one theorem hole. No source-library module is changed.

## Status

landed 20261025T123239-L-1846000 2026-10-25 (merge of deliver/K6/Sheaf.Paper.TensorHomExchange)
