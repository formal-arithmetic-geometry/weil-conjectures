# free_complex_mod_nonzerodivisor_exact (public imports)

## Reason

The second reading found that `Matrix.ToLin` supplies much more than this
coordinate matrix statement and proof need. Import `Data.Matrix.Mul` and the
ideal quotient directly; `Matrix.Defs` is transitively supplied by `Mul`.
No existing declaration signature or definition changes. No target meaning
changes or reopened statement review is needed.

## Old

```lean
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
```

## New

```lean
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Quotient.Basic
```

All other imports and the entire theorem signature are unchanged. This removes
public access to unrelated `ToLin` declarations through this module; the actual
signature dependencies remain public.

## Users

`tools/downstream.py Sheaf.RingTheory.FreeComplexModNonzerodivisorExact --direct
--uses free_complex_mod_nonzerodivisor_exact` lists exactly one direct importer
and no other external declaration user. That importer imports this module
privately, so it does not re-export these imports to its own downstream users.
It has independent determinant and regular-sequence imports for its statements.
Compiled a scratch copy of the unchanged importer against the newly compiled
item in an isolated scratch sandbox with `lcompile.py --all`: both files compile
with no errors or warnings. Thus no adaptation is needed, and downstream
statement meanings and public signatures are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExactFreeComplexLastMinors | unclaimed in this checkout | Unchanged source compiles against the narrowed imports; theorem signature unchanged; private import prevents public export propagation. |
| Sheaf.RingTheory.FreeComplexModNonzerodivisorExact | F4 | Proof closed; public import cleanup only; theorem signature unchanged. |

## Status

landed 20261013T002357-L-2376469 2026-10-13 (merge of deliver/F4/Sheaf.RingTheory.FreeComplexModNonzerodivisorExact)
