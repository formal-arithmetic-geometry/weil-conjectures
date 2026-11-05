# BZ103 progress

- Branch: `u9/BZ103`; starting commit: `4f9f7e361`.
- `LowerStarOpenStalk` and `FrobeniusDecomposition` passed remote `ucheck-bump` at `d546defb406537251ea9a99e3e8b7b8e59d8ee01`.
- Resuming after the user explicitly requested completion following the concrete derivative statement and duplicate dependency proposals.
- Applied `derivative K` → `derivative (R := K)` in the one remaining statement occurrence, preserving the proposition and binders.
- Removed the duplicate project `Algebra.IsSeparablyGenerated` definition in `FieldTheory/SeparableExtension.lean` and publicly imported Mathlib's class replacement. This dependency repair is necessary for `BertiniCurve` imports.
- `AlternatingEulerProduct` passed in the resumed all-module build; the duplicate import conflict is resolved.
- Added `rw [Ideal.under_def] at hQP` in `BertiniCurve` to normalize the new lying-over API equality.
- All four assigned modules will be validated together with `ucheck-bump`; no local Lean/Lake execution.
- Fix patterns and whole-tree counts: `/home/ubuntu/u9/bz/FIXES-BZ103.md`.
- No DONE marker until all four assigned modules pass.
