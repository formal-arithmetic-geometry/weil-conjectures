# Scalar tensor powers by ordinary recursion

## Reason

`Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions` is unclaimed. Its
`scalarTensorPower` definition compiles to `Nat.brecOn`, as confirmed by `#print`.
Repeated dependent reduction of powers contributes to the signed-line module's
compile-limit failure. Replace the recursion mechanism with `Nat.rec`, retaining
left association, the scalar unit at zero, the original module at one, and the
three computation equations. This changes the presentation of data used
by the targets, so the interpretation review should inspect the preservation
argument and these equations. No target statement or hypothesis changes. No
adopted source-library module is edited.

## Old

```lean
noncomputable def scalarTensorPower (R : Sheaf J CommRingCat.{u}) (M : Mod R) : ℕ → Mod R
  | 0 => 𝒪 R
  | 1 => M
  | n + 2 => 𝒯 (scalarTensorPower R M (n + 1)) M
```

## New

```lean
noncomputable def scalarTensorPower (R : Sheaf J CommRingCat.{u}) (M : Mod R) : ℕ → Mod R
  | 0 => 𝒪 R
  | n + 1 => Nat.rec M (fun _ P ↦ 𝒯 P M) n
```

The positive-power branch is an explicit ordinary recursor. Its zero, one and successor-by-tensor
computations all hold by reflexivity. No client source refers explicitly to the former
generated equation-lemma names. Public computation theorems `scalarTensorPower_zero`, `scalarTensorPower_one` and
`scalarTensorPower_succ` state the original three equations, with proofs by reflexivity.
Their Lean attachments are added to the existing data node.

At zero the result is the scalar unit. At one the positive recursor is evaluated at zero and returns `M`. At `n+2` the step tensors the value at `n+1` on the right by `M`.
Thus induction identifies every value with the former definition; in particular
zero rings, zero modules and all site universes retain exactly the same objects
up to equality. There are no new assumptions, choices or holes. Every other
existing definition and declaration signature in this module remains unchanged.
A separate verification lemma compares the new and former recursors by induction.
The earlier consolidation recorded in
`coord/changes/P2-canonical-coefficient-tensor-powers.md` remains in place.

## Users

There are six direct importers, twelve textual users (including the defining
module and the item), and 2621 transitive importers in the inspected source.
The union of direct importers and textual users is listed below. Each is
unclaimed except the item held by X8. All receive the same unit, degree-one
module and successor tensor equations; statements keep the same mathematical
meaning. Two unclaimed consumers require the proof adaptations described below.

| Module | Holder | Effect |
|---|---|---|
| Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions | unclaimed | Recursion mechanism changed; existing computation API preserved. |
| Sheaf.Paper.SignedLineScalarTensorTower | X8 | Complete proofs use the new computation mechanism. |
| Sheaf.Algebra.Homology.StrictScalarHomChain | unclaimed | Direct importer; unchanged. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Direct importer and textual user; unchanged. |
| Sheaf.Paper.CommonLinePositiveScalarPowers | unclaimed | Forced `rw` to `erw`; no interface change. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Direct importer and textual user; unchanged. |
| Sheaf.Paper.InvertibleTensorScalarExtension | unclaimed | Three forced simplification edits; no interface change. |
| Sheaf.Paper.ScalarExtensionBinaryCoherence | unclaimed | Direct importer and textual user; unchanged. |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | unclaimed | Textual user; unchanged. |
| Sheaf.Paper.CompletedLineTensorCoherence | unclaimed | Textual user; unchanged. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Textual user; unchanged. |
| Sheaf.Paper.SignedLineScalarPullbackSquare | unclaimed | Textual user; unchanged. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Textual user; unchanged. |

The private all-exponent equality proof compiles with the new definition. The definition
and its explicit computation API compiled in 26.1 seconds. The original
`InvertibleTensorScalarExtension` proof fails after unfolding the new recursor: binary
naturality cannot match `scalarTensorPower R M (r+1)` against an exposed `Nat.rec`.
Its zero and one simplifications now use the named equations, and its successor step
uses `simp only [scalarTensorPower_succ]`. This preserves the dependent intermediate types;
the adapted file compiles in 27.1 seconds. `CommonLinePositiveScalarPowers` fails at its
successor `rw` for the same exposed positive-power type mismatch. Replacing that single
`rw` with `erw` permits the definitional equality; it compiles in 38.5 seconds.
These are the only consumer proof changes. Signatures, visibility and definition bodies
of both consumers stay unchanged. The unchanged consumers `CoefficientTwistsDetailed`, `IntegralLineReductionDefinitions`,
`IntegralLinePowerComparisons` and `SignedLineScalarPullbackSquare` compile against the
new recursor in 56.6, 24.5, 40.0 and 19.2 seconds respectively. Checks of
`StrictScalarHomChain`, `CompletedLineTensorCoherence`, `ScalarExtensionFunctor`,
`SignedLineDerivedBaseChange` and `ScalarExtensionBinaryCoherence` reach the 60-second
limit; the earlier byte-identical original-source controls also reach that limit.
These checks provide no evidence of a new regression. Byte-identical verification copies
have been removed from the packet.

## Status

landed 20261024T191739-L-484068 2026-10-24 (merge of deliver/X8/Sheaf.Paper.SignedLineScalarTensorTower)
