## What changed

Replaced the proof hole of `AlgebraicGeometry.ProEtale.kummer_strict_adjunct_compatibility`
by an assembly proof from the quotient-normalized evaluated reduction unit and the
normalization of the strict Kummer target on that unit. Existing declaration names,
signatures, attributes and definition bodies are preserved. The four definitions move verbatim to
`Sheaf.Paper.KummerStrictAdjunctData`, which the item publicly imports. The item
keeps its existing public import and adds two proof imports.

The new proved module `Sheaf.Paper.KummerAdjunctFromUnit` has the public theorem
`kummer_adjunct_from_unit`. Its private lemma
`evaluated_unit_ext_naturality` performs the derived-category calculation:
naturality on `f.hom`, cancellation of the source comparison, and
insertion of the negative target unit equation give the negative Yoneda product.
The remaining calculation maps the supplied residue-lift equality through exact
forgetting, compares composite exact functors using the existing proved Ext
composition theorem, substitutes the specified equation for `g`, and cancels
`s.hom` against `s.inv`. No derived fullness or equality detection by finite
levels is used.

Added `Sheaf.Paper.DiagonalEvaluationUnit`, containing the actual evaluated
forgetting functor, the ordinary quotient unit, and a structure recording a
natural transformation with its cochain-counit and single-object equations.
Added `Sheaf.Paper.StrictKummerUnitNormalization`, whose conclusion concerns
only the strict roots target and the unit at shifted comparison units.
The finite-forgetting comparison is an explicit irreducible identity-component
isomorphism with a proved HEq transport API, so the concrete assembly need not
repeatedly unfold the sheaf constructions.

A proved private assembly lemma in the item performs the existential elimination
over abstract categories before the concrete specialization. Profiling showed that
expanding those witnesses directly at the sheaf types caused excessive kernel
checking; the abstract assembly shares those constructions.

Neither remaining theorem is the old arbitrary-source/residue-lift formula under
another name. The first has no Kummer data; the second has no source `S`,
source isomorphism `a`, residue object `Q`, maps `s` or `g`, or classes `f` and `e`.
The arbitrary-arrow part is proved by the new generic naturality theorem.

Final `lcompile.py --all` completed without errors or warnings. Actual compile
times were 27.1 s for the relocated data, 29.5 s for target normalization, and
23.1 s for the item. The proved generic naturality module previously compiled
in 3.9 s and the unit module in 11.1 s. The unchanged direct importer
`Sheaf.Paper.KummerStrictTargetTransport` compiled against the packet in 43.1 s.
Its temporary source copy was removed before delivery. All profiler and trace
options have been removed. The required `deliver3.py` performs the delivery checks.

## Proved and sorry left

Closed the original hole of
`AlgebraicGeometry.ProEtale.kummer_strict_adjunct_compatibility`
(node `lem-sfb-kummer-strict-adjunct-compatibility`). The item has zero remaining
proof holes. Its original statement is unchanged.

Added two holes, both whole named public theorems in their own new modules:

- `AlgebraicGeometry.ProEtale.diagonal_evaluation_unit_exists`
  (`lem-sfb-diagonal-evaluation-unit`): construction and normalization of the
  underlying unit of evaluated simultaneous reduction.
- `AlgebraicGeometry.ProEtale.strict_kummer_unit_normalization`
  (`lem-sfb-strict-kummer-unit-normalization`): the strict roots comparison and
  its normalization only at shifted comparison units. The real proposition
  definition `KummerUnitNormalizedTarget` keeps coefficient expressions as
  parameters during concrete specialization; its body is the roots witnesses
  and unit equation.

This is a decomposition: one old hole closed, two strictly smaller holes added,
net minus one hole closed. It is not a complete proof of the Kummer comparison.
Both new docstrings give the source and the remaining argument. The generic
naturality theorem and all its private helpers are proved. No definition contains
a proof hole or chooses data from an unproved mere-existence theorem. Choices of
unit witnesses occur only inside the theorem proof.

## No longer needed

No module is withdrawn or globally pruned, and no existing import is removed.
The item's previous direct proof dependencies on K-flat resolution, two-term
coefficients, Kummer exactness, site comparison, constant-ring equivalence,
roots and truncation, and single-exponent divisible reduction move into the
new statements where they are needed. They are not claimed to be mathematically
unnecessary. The assembly instead directly uses the two new nodes, the diagonal
system interface, and the new proved generic naturality theorem, whose proof uses
the existing proved exact-functor Ext composition theorem.
The unit route, including the computation of strict transitions, is preserved.

## Where the brief, the DAG or earlier work was wrong

No existing statement is disputed or weakened. The earlier plan put the
construction of the quotient-normalized evaluated unit and its Kummer target
normalization together with arbitrary-arrow naturality in one hole. The formal
naturality calculation separates those responsibilities.

The existing normalized Kummer target results for variable coefficient-system
modules were read. They do not directly specialize to an arbitrary supplied
`DiagonalDerivedReduction` valued in strict constant-p-adic systems; the
comparison with that supplied universal counit remains part of the new unit
construction. The single-exponent reduction theorem also does not itself
provide the strict transition comparison.

The edge cases of the two remaining statements were checked: an empty scheme
has zero sheaves and the same quotient constructions; `n = 0` has positive
exponent `n + 1`; the sign uses additive negation and requires no division by two.
There is no torsion-freeness condition on arbitrary sources: the degree-zero
unit equation holds whether or not the source counit is invertible, and the
assembly uses its supplied inverse only when the original statement supplies it.

## New nodes

`lem-sfb-diagonal-evaluation-unit`, in the original chapter and unit, records
`Sheaf.Paper.DiagonalEvaluationUnit`. Its statement introduces the ordinary and
derived quotient units and both comparison equations. Its proof plan retains
the K-flat, coefficient-resolution and constant-ring-equivalence dependencies.

`lem-sfb-strict-kummer-unit-normalization`, in the original chapter and unit,
records `Sheaf.Paper.StrictKummerUnitNormalization`. It retains the full strict
roots transition and root-to-line equation, but its derived equation concerns
only the evaluated unit at shifted comparison units. Its proof plan retains
Kummer exactness, truncation and the positive single-exponent normalization.

`lem-sfb-kummer-adjunct-from-unit` records the proved generic naturality theorem.
It uses only the existing exact-functor Ext composition theorem and formal
category/shift/Ext identities. It has no proof hole.

`def-sfb-kummer-strict-adjunct-data` records the four relocated definitions.
They retain their names and bodies and remain publicly available through the
original item module. This permits the new normalization theorem to use the
named positive Kummer class without expanding its coefficient constructions.

Mathlib searches and their actual results are recorded in the new nodes and
`searches.jsonl`. Blueprint searches for the normalized unit found no existing
node with either exact statement. The definition relocation and added public
import are recorded in
`coord/changes/F5-kummer-strict-adjunct-data.md`. No statement or definition
meaning, instance or global attribute changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalEvaluationUnit": "1c105030a73d47e825241096310710cd62ded7fb", "Sheaf.Paper.KummerAdjunctFromUnit": "6e8b70c30b2ac238bad7149eb30179c1ba8104d6", "Sheaf.Paper.KummerStrictAdjunctCompatibility": "35ec62ed52498a1f3e32c1242de43501913d5465", "Sheaf.Paper.KummerStrictAdjunctData": "91cbfd75e3088a9293f9bbfe25ba0bd981d015df", "Sheaf.Paper.StrictKummerUnitNormalization": "6eeac958be8736c4f04d6cfd9654491ce698cce5"}, "results": {"Sheaf.Paper.KummerStrictTargetTransport": {"hash": "c3acf640e338a9800053af8db021062f6f64b52c", "status": "SLOW"}}, "seconds": 72, "time": "2026-10-28T00:35:23+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
