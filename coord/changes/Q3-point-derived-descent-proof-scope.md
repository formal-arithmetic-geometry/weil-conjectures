# Point-derived descent: private proof scope

## Reason

The interface checker conservatively flags the new `section`, `variable`, and local
`attribute` commands used by the fully proved private comparison helpers. This record
accounts for those commands. The public declarations, their signatures, all definition
bodies, all existing docstrings, and all public imports remain verbatim. No source-library
module is changed.

Keeping the generic scalar comparison inside the point-specific parameter context made
unification of the published scalar witness exceed the 60-second compile limit. Placing
it before that context, and recording the raw published universal pair for final kernel
conversion, makes the full proof compile in 29.9 seconds. An alternative canonical-pair
version in the same scope also compiled in 30.1 seconds. This changes proof elaboration,
not the mathematical interface.

## Old

After `namespace WeilConjectures`, the file immediately entered
`namespace PointDerivedSectionsTensor`. It had no private scalar-comparison section or
local irreducibility attributes. The final theorem had one `sorry`.

The public definitions were `PointDerivedSectionsTensor.sectionsE`, `sectionsL`, `A`,
`B`, and `PointDerivedSectionsTensorData`. Their complete original source is retained.
The final public theorem is `WeilConjectures.point_derived_sections_tensor_descent`;
its complete original signature is retained.

## New

Before the point-specific declarations, a closed `section ScalarComparison` contains
only these coefficient parameters:

```lean
variable {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}
```

It contains two proved private theorems, `exact_derived_comparison` and
`scalar_exact_comparison`, and the proof-local attribute:

```lean
attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted
```

The section closes before every existing public declaration. The same local attribute
is used before the private descent-assembly theorem. These attributes do not export a
new reduction rule, instance, or visibility change to importers. Other new helpers are
also private and proved. Private proof imports replace the obsolete proof dependencies
listed in report.md. The completed theorem uses these helpers; no statement or data
construction is weakened or replaced.

## Users

`python3 tools/downstream.py Sheaf.Paper.PointDerivedSectionsTensorDescent --uses
WeilConjectures.point_derived_sections_tensor_descent
WeilConjectures.PointDerivedSectionsTensorData
WeilConjectures.PointDerivedSectionsTensor.sectionsE
WeilConjectures.PointDerivedSectionsTensor.sectionsL
WeilConjectures.PointDerivedSectionsTensor.A
WeilConjectures.PointDerivedSectionsTensor.B` reports one downstream module:
`Sheaf.Paper.PointDerivedTensorTowerCoherence`.

| Module | Review and effect |
| --- | --- |
| Sheaf.Paper.PointDerivedSectionsTensorDescent | Q3's assigned item; one proof completed. All existing public declarations retain their types, visibility, and definition bodies. |
| Sheaf.Paper.PointDerivedTensorTowerCoherence | Its Comparisons structure uses the unchanged PointDerivedSectionsTensorData and later definitions use its unchanged exactness fields and point-section aliases. The textual B hits also include its own local variable B. None of its statements becomes weaker, stronger, or different; no adaptation is required. |

There are no other downstream modules in the current source. No target statement or
used definition changes, so no target-meaning review is reopened. The assigned node's
statement and Lean attachment are unchanged; only proof, proof_deps, proof_origin, and
tool_uses describe the shorter proof. There are no forced adaptations or new nodes.

## Status

landed 20261021T225206-L-3792800 2026-10-21 (merge of deliver/Q3/Sheaf.Paper.PointDerivedSectionsTensorDescent)
