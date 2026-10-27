## What changed

Proved `LocalizedModule.exists_gradedLocalization_scalarExtension_equiv` without changing its statement. The proof constructs both homogeneous fraction submodules, restricts the ordinary localization comparison, proves injectivity by tensoring a retraction, and proves surjectivity by induction on tensors of homogeneous numerators. Its final fraction formula is the original normalization.

Added two supporting modules, `Sheaf.Algebra.Module.HomogeneousLocalizationRetraction` and `Sheaf.Algebra.Module.LocalizationScalarExtensionCoefficients`, with proofs of the homogeneous projection and ordinary localization comparison. Updated the item's DAG proof to this route. No existing module besides the item was changed; its public imports and declaration signature are unchanged.

## Proved and sorry left

Closed the original hole in `LocalizedModule.exists_gradedLocalization_scalarExtension_equiv` (node `lem-sfb-graded-module-localization-scalar-extension`). Added no holes. The two new public theorems `LocalizedModule.exists_homogeneousPieceAway_retraction` and `LocalizedModule.exists_localization_scalarExtension_coefficients_equiv` have complete proofs. No `sorry` remains in the delivery, and no statement was split off with `sorry`.

The three modules compile in import order (5.2 s, 9.2 s, and 11.6 s respectively), below the 60 s limit. The final delivery preflight checks every delivered declaration for the permitted axioms. No signature, definition, or public import of an existing module was changed.

## No longer needed

Removed the proof imports `Mathlib.CategoryTheory.Limits.HasLimits`, `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`, and `Mathlib.CategoryTheory.Monoidal.Closed.Braided`.

The item no longer uses `def-weil-pbc-category-colimit` or `lem-weil-pbc-tensor-commutes-with-colimits`. The explicit ordinary-localization comparison and split homogeneous projection replace the sequential-colimit argument. These nodes may still serve other items; no module or DAG node is withdrawn. Both original statement dependencies remain needed. No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The original colimit plan is valid, but a shorter formal route uses `IsLocalizedModule.rTensor`, restriction of scalars, and projections from the internal grading. The retraction is defined on fractions by projecting x/f^m to the numerator component of degree j+md. Its well-definedness is proved using the full localization relation, including an extra annihilating power; it never cancels f on M. Thus nilpotent denominators, zero coefficient rings, negative j, unbounded gradings, and nonflat coefficient extension are included.

## New nodes

`lem-sfb-homogeneous-localization-retraction`, in `dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-localization-retraction.json`, records the split inclusion of any homogeneous localized piece. It is realized by the fully proved theorem in `HomogeneousLocalizationRetraction.lean`.

`lem-sfb-localization-scalar-extension-coefficients`, in `dag/nodes/sec-six-functors-basics/lem-sfb-localization-scalar-extension-coefficients.json`, records the ungraded localization comparison with its fraction formula. It is realized by the fully proved theorem in `LocalizationScalarExtensionCoefficients.lean`. Both nodes inherit the item's chapter, unit, and blueprint origin and record the Mathlib searches.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Module.GradedLocalizationScalarExtension": "c8fa153e9b4215dafc118eccfc0406f8dffe7e36", "Sheaf.Algebra.Module.HomogeneousLocalizationRetraction": "8cfa3efa6d69ee0ad140e8e1a5ca6371bf36a726", "Sheaf.Algebra.Module.LocalizationScalarExtensionCoefficients": "6ae68a1bdf25a74e597408b83b9cda87363b31f9"}, "results": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison": {"hash": "c09a52b2f614e7a2c24c0a3c0cdf6c04d08ebb84", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T00:08:17+0800", "transitive": 0, "version": 1}
```

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
