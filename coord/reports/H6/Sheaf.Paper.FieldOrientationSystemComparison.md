## What changed

Reduced the one remaining hole in
`AlgebraicGeometry.ProEtale.FieldOrientationSystem.field_orientation_system_comparison`.
The existing theorem statement, its docstring, and the already proved
`shifted_sheaf_map_ext` are unchanged.

The original module now proves the actual tower orientation equation from finite
orientation equations. The new proved private helper
`evaluation_single_shift_naturality` spells out naturality of exact evaluation's
single/shift comparison. The proved private helper `presented_map_ext` uses fullness
of the shifted single embedding to represent maps by sheaf-system maps, applies
finite single/shift faithfulness, and uses `shifted_sheaf_map_ext` for componentwise
extensionality. In the theorem, conjugation by the line comparison and the canonical
heart presentations reduces its two orientation arrows to this helper. Cancelling
the line isomorphism gives equality of the actual derived tower arrows.

Both finite coefficient-unit Tor clauses are proved directly by the new private
`coefficient_unit_tor`: tensoring with the unit is isomorphic to the identity, and a
sheaf placed in degree zero has no other cohomology. The helper reuses the existing
`smoothPurityUnitIso`. The exceptional transpose definition is locally irreducible
in the parent proof so rewriting uses its interface without expanding the adjunction.
No imported definition or its global transparency is changed.

Two proper subarguments remain as public theorems in new modules:
`FieldOrientationSystemComparisonData` constructs normalized unit/line comparisons
and their finite equations; `FieldOrientationSystemRigidity` establishes concentration,
heart induction, and uniqueness for a single field. The latter is applied separately
to E and F. Neither is the original assertion with renamed or repackaged hypotheses:
the first stops at finite equations, and the second has only one coefficient field
and no scalar extension or comparison equation. Each has its source, a complete
proof in words, and a matching DAG node.

Validation: both new statement modules compiled, and the final parent module compiled
through `lcompile.py` in 55.9 seconds, below the 60-second limit. Profiling options
were removed before that compile. The first delivery check compiled all three files
and requested three proof-local `letI`-to-`let` style cleanups; these have been applied.
The delivery checks compile the submitted files again.

## Proved and sorry left

The initial item contained one hole, `field_orientation_system_comparison` (node
`lem-sp-field-orientation-system-comparison`). Its body is now a complete proof from
the two smaller statements and the categorical argument described above. This is a
decomposition, not a fully closed proof of the orientation theorem.

Two new holes remain:

- `AlgebraicGeometry.ProEtale.FieldOrientationSystem.field_orientation_comparison_data`
  (`new-sp-field-orientation-comparison-data`);
- `AlgebraicGeometry.ProEtale.FieldOrientationSystem.field_orientation_system_rigidity`
  (`new-sp-field-orientation-system-rigidity`).

Thus one original hole is decomposed into two; zero original holes are fully proved,
and the net hole change is +1. `shifted_sheaf_map_ext` was already proved by N1 and is
preserved verbatim. No `sorry` occurs in a definition or a private theorem.

## No longer needed

Removed the original module's proof-only imports of
`Sheaf.Paper.FieldScalarNormalizedSystems`, `Sheaf.Paper.FiniteOrientationReduction`,
and `Sheaf.Paper.StrictLineHeartAssembly`: these subarguments belong to the two new
nodes. They remain necessary transitively and are not proposed for withdrawal.
Also removed duplicate proof-only Mathlib imports of ExactFunctor and FullyFaithful,
already publicly exported by FieldOrientationSystemHeart.
No existing module, declaration, or DAG node is pruned. The original public imports
remain because they form the existing statement interface.

## Where the brief, the DAG or earlier work was wrong

The previous N1 report correctly noted that
`field_exceptional_system_comparison` supplies some models and adjoints, whereas the
orientation theorem quantifies over supplied D, b, a, A. The finite-equation lemma
must derive its evaluation equation from the supplied normalization fields; it may
not apply that existence theorem to arbitrary supplied models. Its proof in words
records evaluation of the actual counit transpose using `b.scalarEvaluation` and
`A.counit`. This interface work remains in its named hole.

Checked edge cases of the new statements: d=0 retains the coefficient unit and zero
shift; n=0 means the first positive exponent; E=F gives the canonical scalar unitor;
ramification uses the original quotient normalization and no flat quotient hypothesis;
empty schemes give zero sheaves and the same componentwise argument. No target,
existing definition, or existing theorem signature changed. The unit route is kept.

## New nodes

`new-sp-field-orientation-comparison-data`: the normalized scalar comparison and
finite orientation-square subargument, before derived equality detection. Its module
is `Sheaf.Paper.FieldOrientationSystemComparisonData`.

`new-sp-field-orientation-system-rigidity`: the concentration, canonical heart, and
uniqueness subargument for one field, independent of coefficient extension. Its module
is `Sheaf.Paper.FieldOrientationSystemRigidity`.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
