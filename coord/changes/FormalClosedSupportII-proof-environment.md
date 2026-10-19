# Sheaf.Paper.FormalClosedSupportII proof environment

## Reason

The completed proof needs a larger instance-search budget for the derived-category
constructions and opens the internal abelian sheaf-module namespace for private helper
proofs. The preflight conservatively classifies changed top-level commands as an interface
change, so they are recorded here. All public declarations and their signatures remain
unchanged. No declaration, notation, or global instance is added by these commands.

## Old

```lean
@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u vA vB uA uB wA wB


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
```

## New

```lean
@[expose] public noncomputable section

set_option synthInstance.maxSize 4096
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u vA vB uA uB wA wB


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
```

In addition, the following command occurs immediately before the private helper
`formalSupportProductsExact` (there was no corresponding command in the old module):

```lean
open CategoryTheory.InternalAbelianSheafModule
```

The additional option prevents instance synthesis from timing out in the private product
and derived-functor helpers. The namespace opening makes the existing internal module
equivalence declarations available by their documented short names. No public theorem,
definition, instance signature, or statement changes.

## Users

`tools/downstream.py Sheaf.Paper.FormalClosedSupportII --uses formalClosedSupportII
ClosedSupportIIAssertions formalClosedSupportIITensor_commShift` found 220 downstream
modules. Each of its three declaration-use lists contains only the item itself. The
declarations retain identical signatures and meanings, so no downstream adaptation is
required, including in the three direct importers `UniformConstructibleExt`,
`UniformConstructibleExtIntegral`, and `UniformConstructibleExtTorsion` in `Sheaf.Paper`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FormalClosedSupportII | M2 | Private proof elaboration only; public interfaces unchanged. |

## Status

landed 20261019T005340-L-2755332 2026-10-19 (merge of deliver/M2/Sheaf.Paper.FormalClosedSupportII)
