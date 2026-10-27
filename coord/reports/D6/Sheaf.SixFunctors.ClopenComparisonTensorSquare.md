## What changed

Replaced the single sorry in
`SheafOfModules.ClopenComparisonTensorSquare.clopenComparisonTensorSquare`
by a proof from normalized data existence and the four tensor equations. The
assigned theorem's complete signature is unchanged. The seven original definitions
were moved verbatim to `ClopenComparisonTensorSquareData` and publicly re-exported;
only their blueprint owner references changed. A text comparison verifies their
fields, bodies, binders and universes are identical. No source-library file changed.

`ClopenComparisonTensorSquareEquations` proves the localized unit/counit
normalization, the clopen tensor identity, composite-open identity, and full alpha
identity by adjunction transposes, tensor naturality and actual map pasting.
`ClopenCartesianTensorSquare` proves the Cartesian open tensor identity from the
separate compatibility of canonical pullback tensor maps with theta.
`ClopenComparisonTensorSquareDataExistence` constructs the open tensor data for
arbitrary supplied extensions, builds the composite comparison and proves its
transpose formula, using the two separate construction results listed below.
The open tensor construction applies existing normalized operations to an identity
square with a terminal target coefficient ring; it does not assume a proper
projection formula. All arguments work on the whole ringed site for both Modes.

The construction and coherence lemmas use private proof imports. There are no
forced adaptations. The interface move and its consumer check are documented in
`coord/changes/D6-clopen-tensor-interface.md`.

## Proved and sorry left

Original holes closed: one,
`SheafOfModules.ClopenComparisonTensorSquare.clopenComparisonTensorSquare`
(`lem-sf-clopen-comparison-tensor-square`). This is a decomposition, not a
hole-free proof of the original item: three independent lower holes are added.
No sorry remains in the assigned module or the data-existence, Cartesian-square,
and equations modules.

Public theorems proved in the delivery are `data_nonempty`, `cartesian_tensor`,
`equations_for_data`, and `clopenComparisonTensorSquare`, all in namespace
`SheafOfModules.ClopenComparisonTensorSquare`. Proved private helpers are
`open_tensor_exists`, `assemble_data`, `derived_counit_normalization`,
`clopen_tensor`, `composite_open`, and `equations_of_factors`.

The complete remaining-hole list, three added holes, is:

- `SheafOfModules.ClopenComparisonTensorSquare.canonical_pull_tensor`, in
  `CanonicalPullTensor`, node `lem-sf-canonical-pull-tensor`. This is the canonical
  tensor-pullback construction for one supplied arbitrary geometric pullback,
  with both its pure-unit and signed-total representative formulas.
- `SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction`,
  in `ClopenReverseModuleAdjunction`, node
  `lem-sf-clopen-reverse-module-adjunction`. This is an ordinary module-level
  reverse adjunction for one clopen immersion, with its normalization, before
  any derived tensor identity.
- `SheafOfModules.ClopenComparisonTensorSquare.pullback_tensor_compatibility`,
  in `ClopenPullbackTensorCompatibility`, node
  `lem-sf-clopen-pullback-tensor-compatibility`. This is tensor compatibility of
  theta alone on arbitrary ambient objects. It involves no beta, gamma, rho,
  deltaK or full clopen comparison equation.

Each remaining theorem has exactly `:= by sorry`, a complete natural-language
proof and source in its docstring, and its own node and module. None repackages
the original theorem. No definition selects an arbitrary witness from an unproved
existence statement; all existential elimination here occurs inside theorem proofs.
The empty piece, empty complement and zero ring cases require no nonzero/unit
hypotheses in these statements. The pullback construction allows nonflat ring maps;
only the chosen resolving representatives are flat and K-flat.

## No longer needed

No existing node or module is withdrawn. No unit-level route is bypassed.
The original private imports `RingedProjectionTensorStructure` and
`ProEtaleClopenRingedModuleGluing` are no longer direct imports of the assigned
module; their mathematical roles remain in the proof plans for the lower
construction and compatibility results, so they are not claimed as pruned.
The original four public imports are supplied transitively by the new data module.
There are no imports of unused extra proof dependencies in the finished formal
pasting modules. No global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The dependency declarations do not directly provide the supplied-presentation
interfaces needed by this theorem. The canonical unbounded pullback theorem in
`RingedTopoiCanonicalTensorPullbackOfUniverses` uses an explicit algebraic inverse
image and scalar-extension object/map presentation; `Pullback` instead supplies
an arbitrary left adjoint and arbitrary universal left-derived presentation.
Uniqueness transport must also preserve the pure-unit and representative formulas.
The new canonical-pullback node records precisely that remaining transport work.

The gluing dependency is stated on ordinary pro-etale module categories with
base-change presentations; the required statement uses literal open restriction
and must also hold for arbitrary rings on the vertical sequence site. The reverse
adjunction lemma isolates that ordinary, pre-localization construction. The fully
formal derived normalization and clopen tensor argument are provided here.

The tensor-structure interface uses a different ringed-corner presentation and
flatness interface. The remaining theta tensor equality is stated on the actual
independent-universe site and its existing supplied models. The Cartesian mate
calculation above it is proved, rather than left as another identical square.
No statement is disputed, weakened or strengthened. A closure-wide DAG check
also encountered an existing unrelated cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. Checking each of the delivery
added edges separately finds no newly created cycle.

## New nodes

`def-sf-clopen-comparison-tensor-data` owns the seven unchanged definitions in
`ClopenComparisonTensorSquareData`. It avoids an import cycle between the assigned
theorem and the independent construction/coherence statements.

`lem-sf-canonical-pull-tensor` owns `canonical_pull_tensor` in
`CanonicalPullTensor` (namespace as above): ordinary adjoint and derived-presentation transport of the
canonical tensor pullback theorem, one of the three remaining holes.

`lem-sf-clopen-reverse-module-adjunction` owns the reverse ordinary clopen
adjunction in `ClopenReverseModuleAdjunction`, one of the three remaining holes.

`lem-sf-clopen-pullback-tensor-compatibility` owns the canonical tensor equality
under theta in `ClopenPullbackTensorCompatibility`, the third remaining hole.

`lem-sf-clopen-cartesian-tensor-square` owns the proved formal inverse-mate
calculation in `ClopenCartesianTensorSquare`, reducing the Cartesian tensor square
to theta tensor compatibility.

`lem-sf-clopen-comparison-tensor-data-existence` owns the proved assembly theorem
in `ClopenComparisonTensorSquareDataExistence`, including construction and
normalization of the two open tensor comparisons and their composite.

`lem-sf-clopen-comparison-tensor-square-equations` owns the proved derived
adjunction and tensor-pasting argument in `ClopenComparisonTensorSquareEquations`.
All new nodes refine the original seven-step argument below the same blueprint
projection-coherence route. Change record:
`coord/changes/D6-clopen-tensor-interface.md`.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
