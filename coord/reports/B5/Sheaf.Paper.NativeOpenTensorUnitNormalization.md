## What changed

Proved the supplied native open tensor unit normalization from its recorded presentation.
The theorem's entire signature is byte-for-byte unchanged. All existing public imports remain.
Only the assigned module, four new proof modules, and their DAG records are delivered.

The private adapter transports the native tensor data through explicit canonical expression
equalities. The equality proofs live in a separate proved module. A private specialization keeps the
exact functors abstract during the tensor-data conversion, before substituting the concrete
open extension and restriction; this bounds kernel checking without changing any data.

The proof first totalizes `s.sheaf_inverse`, testing the identity on each actual homogeneous
coproduct insertion and using the supplied comparison summand equations. A generic localization
lemma then combines the two recorded model squares, naturality of the specified native model,
and the exact localized adjunction unit. Naturality transports the resulting equation from
K-flat representatives to all derived inputs.

The representative existence step is also proved. A private abstract transport lemma
keeps the native equivalence and tensor comparison abstract while checking both tensor tests:
 transport an existing independent-coefficient
ringed K-flat resolution through the native ringed equivalence. The total tensor comparison,
signed flip, symmetry, and tensor mapping-cone comparisons verify both native K-flat tests.
This argument does not assume a calculus of fractions on the category of complexes.

Edge cases checked in the arguments: zero complexes, zero tensor summands, the empty scheme,
and unbounded complexes. Totalization uses all integer-indexed summands; no boundedness,
nonemptiness, or choice of a nonzero generator is assumed. The generic localization step only
cancels isomorphisms and transports natural equations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_unit_normalization`.

Added zero holes and split off zero unproved statements. All four new modules are proved.
No `sorry` remains anywhere in this delivery. This is a proof from the existing library's
recorded declarations, not a claim that all their transitive dependencies are already proved.

## No longer needed

The item's original direct proof dependencies `lem-sf-ringed-slice-tensor-generators`
(`Sheaf.CategoryTheory.RingedSliceTensorGenerators`) and
`lem-sfb-localized-site-tensor-restriction`
(`Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`) are not imported:
the supplied `NativeOpenTensorData` already contains the required normalized sheaf equation.
Reconstructing either sheaf comparison would be redundant and would not identify the supplied
one. These nodes remain needed wherever other proofs use them; no existing module is withdrawn.

`def-weil-exact-derived-adjunction` is now used inside the generic localization helper rather
than as a separate direct proof dependency of the item. Its module remains imported there.

`Sheaf.Paper.NativeWeilTensorRingedKFlatResolution` is not used. Its fraction-calculus clause
is marked statement-disputed; the new representative proof obtains exactly the needed density
without that clause. No upstream declaration is removed or changed.

Removed unused preliminary imports from the new totalization helper:
`Sheaf.Paper.NativeOpenTensorPresentation` and `Sheaf.CategoryTheory.ExactDerivedAdjunction`.
The helper only needs the termwise adjunction and Mathlib totalization. The new representative
module imports `Sheaf.Paper.DerivedWeilTensorOperations` directly instead of the unused
`Sheaf.Paper.NativeOpenTensorOperations` wrapper.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted two pieces of glue: naturality for the specified
`nativeOpenTensorModel`, and density of complexes satisfying both native K-flat tests.
The former follows directly from `nativeDerivedTensor_models`; the latter is proved here
from the genuine ringed resolution theorem, without the disputed fraction-calculus package.
The assigned statement itself requires no correction.

`tools/blueprint_refs.py ancestor` reports no blueprint ancestor for the assigned node.
The new records retain that null ancestor and record the existing normalization chain in
`blueprint.from.via`. Whole-blueprint searches found no matching generic unit normalization
or native two-sided representative statement.

## New nodes

- `lem-sf-open-tensor-unit-totalization`:
  `CategoryTheory.openTensorUnitTotalization`, the homogeneous totalization calculation.
- `lem-sf-open-tensor-unit-localization`:
  `CategoryTheory.OpenTensorPresentation.unit_normalization`, transport through the model
  squares and then along representative isomorphisms. The representative calculation is
  a proved private helper.
- `lem-sf-native-two-sided-kflat-representatives`:
  `AlgebraicGeometry.ProEtaleWeilSheaf.native_two_sided_kflat_representatives`, density using
  ringed K-flat resolutions and both tensor-cone comparisons.

- `lem-sf-native-open-tensor-canonical-data`:
  `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_canonical_data`, the four defining
  expression equalities for the tensor object function, its left map, total, and insertion.

Each node has its complete argument, source, actual Lean attachment, and Mathlib searches.

Validation: all five delivered Lean modules compile individually through `lcompile.py`:
totalization 5.2 s, localization 5.1 s, K-flat representatives 42.2 s, canonical data
17.7 s, and the complete assigned module 24.5 s. Development profiling options were
removed for the delivery. The original theorem signature is unchanged, all delivered
Lean files have zero `sorry`, and all lines are within 100 characters.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.CategoryTheory.OpenTensorUnitLocalization": "016ae4f5972f4344081dbe8a170f25f29fdd81db", "Sheaf.CategoryTheory.OpenTensorUnitTotalization": "a787dcacbddfd97ec722f83dd0907a828f32dbc0", "Sheaf.Paper.NativeOpenTensorCanonicalData": "36342c6fa3418f267a03d618510cfe6f939eb48f", "Sheaf.Paper.NativeOpenTensorUnitNormalization": "15718ede916a236c2d123f5d96b0d205485e48be", "Sheaf.Paper.NativeTwoSidedKFlatRepresentatives": "01c9b44d38bd3b64e8cebb2c14419ea7f276f726"}, "results": {"Sheaf.Paper.NativeOpenTensorForgetNormalization": {"hash": "3fd4b9f7f6f6ee071fdf4e542482e3632ec028a7", "status": "OK"}, "Sheaf.Paper.NativeOpenTensorNormalization": {"hash": "f08a9fdb0425acbb38206b2e3d9a405a8d3b8729", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T14:14:24+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
