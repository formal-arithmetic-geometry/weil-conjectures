## What changed

Reduced `SheafOfModules.SliceTensorGenerator.coherence_exists` to three genuine
parts of its argument: normalized scalar comparisons, normalized ordinary
tensor transport, and ordinary strict tower assembly. The main theorem combines
these parts in Lean. It derives the inverse scalar generator formula by applying
the inverse to the forward formula and using `hom_inv_id`; it derives the scalar
unit equation by specializing the ordinary formula to one. The existing
`Coherence.onComplexes` supplies the degreewise chain comparison.

Moved `extend`, `TensorLift`, `TensorLiftNormalized`, `LinearComparison` and
`LinearNormalized` verbatim into `SliceTensorGeneratorInterfaces`. The original
module publicly re-exports them. This enables independent proof-step modules
without cyclic imports. It is a dependency extraction, not a response to the
60-second compilation limit. The `Coherence` structure and `onComplexes` body
are also byte-identical to current source. No target or adopted source-library
declaration changes. The change record is
`coord/changes/s2-slice-tensor-generator-interfaces.md`.

The retained attempt was inconsistent: report.md claimed a complete proof, while
the item file stopped among private helpers and omitted the main theorem. The
saved full attempt also had errors. All of that work is preserved in scratchpad;
none of its uncompiled claims is counted as proved here.

## Proved and sorry left

Closed the original textual hole in
`SheafOfModules.SliceTensorGenerator.coherence_exists` by decomposition, not by
closing its mathematical dependencies. The combining proof has no holes.
Added three named public holes, each in its own module:

- `SheafOfModules.SliceTensorGenerator.scalarComparisons_exists`
  (`lem-sf-slice-normalized-scalar-comparisons`): scalar restriction and scalar
  extension only, with normalization and uniqueness; no tensor or tower result.
- `SheafOfModules.SliceTensorGenerator.tensorTransport_exists`
  (`lem-sf-slice-normalized-tensor-transport`): the tensor identification on any
  site; no slice extension, coefficient naturality or tower result.
- `SheafOfModules.SliceTensorGenerator.tensorTowerAssembly_exists`
  (`lem-sf-slice-tensor-tower-assembly`): assemble ordinary tower comparisons
  from given normalized scalar and tensor identifications. This does not assert
  that those input comparisons exist and is not the parent statement repackaged.

Actual count: one original hole closed, three new holes added; zero holes remain
in the item module. Net minus two holes, explicitly a decomposition. No `sorry`
is in a definition. The proof selects only witnesses uniquely determined by the
normalization predicates: k and l have explicit uniqueness, t is fixed on all
pure-tensor sheafification generators, and o has explicit uniqueness. They are
local variables of a theorem proof, not arbitrary data in a public definition.

Validation: each intermediate module and the interface compiled. Final main
proof and consumer validation are being completed before submission.

## No longer needed

Removed the original private imports
`Mathlib.CategoryTheory.Sites.PreservesSheafification`,
`Mathlib.CategoryTheory.Sites.LocallyBijective` and
`Mathlib.CategoryTheory.Sites.LocallySurjective`. Original public imports are
preserved by the interface module's public imports. No module is withdrawn.

The parent uses the three new proof steps directly. Its planned sheafification
interface, underlying-set sheafification and local-lift nodes are now needed
only within the intermediate generator arguments, not by the combining proof:
`lem-pc-sites-module-sheafification-interface`,
`lem-pc-sites-sheafification-underlying-sets`, and
`lem-cbc-presheaf-sheafification-epi-local-lifts`. Their existing mathematics is
not withdrawn or claimed globally unnecessary. The parent retains its approved
ringed-generator tool dependency through the tower-assembly node, whose proof
explicitly uses `exists_ringedSliceTensorGenerators`. No unit route is bypassed.

The retained report's semilinear/StrictScalarHomChain alternative is not used;
no imports of those modules are added. This delivery prunes no library module.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no statement is disputed. The
retained report's proof and validation claims were premature. The saved proof
attempts demonstrate the unresolved tensor/sheafification representation glue;
this is now exposed as named proof obligations rather than claimed complete.

Edge cases checked mathematically for all three new statements: no arrows to V,
several arrows and restrictions merging summands, zero modules and rings,
non-flat ring maps, arbitrary transition maps, and unbounded complexes. Direct
sums and tensor maps are additive, so merging summands causes no problem; the
arguments use adjunctions and sheafification, not flatness or global section
lifting. Scalar actions use commutative unital algebra maps throughout.

## New nodes

`def-sf-slice-tensor-generator-interfaces` records the five existing interfaces
moved verbatim to `SliceTensorGeneratorInterfaces`. It adds no mathematical data
or hole; its functor laws use the same proved scalar-extension map laws.

`lem-sf-slice-normalized-scalar-comparisons` records the scalar restriction and
scalar extension parts of parent Steps 2 and 4. Its complete proof in words is
in the node and theorem docstring; actual scalar/tensor representations still
need to be reconciled in Lean.

`lem-sf-slice-normalized-tensor-transport` records the tensor-identification
part of parent Step 3, independently of slice extension and towers.

`lem-sf-slice-tensor-tower-assembly` records the remaining ordinary projection,
normalization, coefficient naturality and tower assembly from parent Steps 3,
5, 7 and 8. Its proof uses the existing ringed generator theorem, preserving the
reviewed ordinary projection route. None of these nodes is the full original
statement under another name.

Change record: `coord/changes/s2-slice-tensor-generator-interfaces.md`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
