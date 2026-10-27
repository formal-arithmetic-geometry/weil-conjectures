## What changed

Completed `AlgebraicGeometry.Etale.exists_etaleScalarFlatModel` without changing its signature.
The proof obtains a finite-value constructible flat model, handles every such representative,
computes the chosen derived scalar extension in the B-module category, and transports boundedness,
constructible cohomology and the exact Tor interval. The ordinary scalar map remains arbitrary.

Added proof imports of ConstructibleCoefficientSiteSquare, the source ScalarExtensionConstructible,
the source etale Finiteness.FlatModel, and ConstructibleEtaleModuleSheafComparison. A proof-only
`import all Sheaf.Paper.WitnessCompatibility` accesses the already constructed scalar derived
adjunction and its K-flat invariance instance. Updated the item's node proof and dependencies.
Existing public imports and all public signatures are preserved.

Validation: complete single-file compilation succeeds without warnings, with no local sorry.
Edge cases need no exclusions: the zero ring, empty scheme and zero object satisfy the same
argument; a=b gives a one-degree model; scalar flatness requires no flatness of B over A.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.exists_etaleScalarFlatModel`
(node `lem-sp-etale-scalar-flat-model`). Added 0 holes; 0 holes remain in the item.
No split-off statements or new declarations. This is a proof from existing library declarations,
including the existing coefficient/site-square theorem, not a claim that its dependency closure
is already sorry-free.

## No longer needed

Removed proof imports `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` and
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`. The corresponding planned nodes
`lem-pc-bounded-above-flat-kflat-site` and `lem-pur-kflat-change-of-rings` are unnecessary here:
the adopted source gives bounded-flat K-flatness directly for ModuleCat-valued sheaves, and
`ProEtale.flat_etaleSheafExtendScalars_obj` gives scalar flatness before applying that criterion
a second time. This avoids transporting between two sheaf-module encodings.

The generic cochain-model theorem of `lem-pur-derived-change-of-rings` is also unnecessary as
a proof dependency: the actual published chosen scalar functor is identified directly with
the constructed scalar derived adjunction from `def-weil-pbc-witness-compatibility`, then computed
by its K-flat counit. Existing public reexports are preserved, so no whole-module withdrawal
or claim that these modules are globally unreachable is made. The unit route is preserved. Obsolete tool_uses entries for these three nodes were removed.

## Where the brief, the DAG or earlier work was wrong

The plan's ringed-site K-flat and change-of-rings interfaces use SheafOfModules, whereas the
item uses ModuleCat-valued sheaves. The source already proves the directly applicable generic
K-flat criterion and etale scalar-flatness result, so those bridges can be avoided.
The published pbcFixedScalarExtension is a chosen left adjoint; uniqueness of left adjoints
is needed to identify it with the actual constructed total left derived functor. The existing
private scalarDerivedAdjunction and scalarExtension_preservesKFlat provide precisely that
construction, accessed solely in the proof. No definition or statement repair was required.

The compile tool initially selected a local mirrored build missing Mathlib.olean. Compiling
through its supported `LCOMPILE_NO_LOCAL=1` remote route succeeded; no tools were modified.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
