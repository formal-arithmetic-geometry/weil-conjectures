## What changed

Completed `AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage`
in `Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel`, without changing its signature.
The model is the actual object `Rf_*(F[0])`. Source-library `PlusCompatibility` proves
connectivity and identifies its cohomology with classical higher direct images.
The existing theorem in `RelativelyFlatCanonicalModuleBaseChange` gives an invertible
map for the given cartesian square. Tensor pullback is additive because its adjunction
makes it right exact. Uniqueness of left adjoints identifies tensor pullback with ordinary
module pullback; applying cohomology finishes the base-change clause.

Added only proof imports of `PlusCompatibility` and
`RelativelyFlatCanonicalModuleBaseChange`. Updated the existing node's proof route.
Removed the saved attempt's private transport helper and dependency-module adaptation.
No public imports, definitions, declaration signatures, or file-level options change.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage`
(node `lem-pc-higher-direct-image-derived-model`). No holes remain in this module;
no new holes were added or split off.

The final module compiles through `lcompile.py` with exit code 0 and no warnings,
including after removing the saved attempt's transparency options.

The proof uses the existing holed theorem
`AlgebraicGeometry.exists_isIso_canonicalModuleBaseChange_of_isFlatOver`
(node `lem-pc-relatively-flat-canonical-module-base-change`). This delivery proves the
item from that existing dependency; it does not close all its transitive dependencies.
The model is explicitly constructed, rather than chosen from an existence theorem.

## No longer needed

The original planned dependency `lem-pc-rf-perfect-base-change` and its module
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` are unnecessary for this proof:
only relatively flat base change is used, without its perfectness assertion.
The saved attempt's dependency `lem-pc-rf-base-change-flat-module` and module
`Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange` are also unnecessary.
Its umbrella-import repair is removed from this delivery.

Removed the saved attempt's proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
and `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange`, together with
`derived_image_iso_pullback`. The `RightDerivedFunctorCompIso'` and
`mapDerivedCategorySingleFunctor` route is not needed. The original module's imports
are retained: each supports the statement or construction of the derived model.
These are local pruning claims, not claims that other targets no longer use these modules.

## Where the brief, the DAG or earlier work was wrong

The original node proposed perfect direct image base change, which imposes unnecessary
perfectness machinery. The saved attempt instead used relatively flat base change, but
that module's public umbrella import reaches this item through
`DirectImage.PerfectLocusOfRank` and creates a cycle. The proposed import repair does not
satisfy the forced-adaptation rule: the unchanged dependency still compiles against the
compiled overlay. The earlier delivery checks correctly refused that adaptation.

The existing canonical module comparison, landed since the earlier attempt, already
handles arbitrary cartesian squares and has no import path back to this item.
Using it resolves the obstruction without adapting a module held by another worker,
adding new nodes, or bypassing a realized unit step. The unit's `realized` lists are empty.
The item's statement and every target statement are unchanged.

## Second reading by P1

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The theorem signature, definitions, and existing declarations are unchanged byte for
byte; only the author line, proof-only imports, and proof body differ. Verdict: pass.

2. **Proof validity and axioms.** Compiled the module with `lcompile.py`; it exits successfully
without warnings. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`, and the proof constructs `E` explicitly as the derived direct image of the
single complex. Verdict: pass.

3. **Statements and dependencies.** No statements were split off or added. The existing
canonical-module base-change theorem is used with its unchanged statement; the homology and
connectivity comparisons are source-library declarations. The node's proof steps and
`proof_deps` match the imports and proof body, and the reported removed dependencies are not
used. Verdict: pass.

4. **Route and pruning.** The proof follows the shortest available route through
`PlusCompatibility` and `RelativelyFlatCanonicalModuleBaseChange`, avoiding the unnecessary
perfect-base-change and transport modules. The module's public imports remain unchanged and the
new imports are proof-only. Verdict: pass.

5. **Unit and source alignment.** The target statement is unchanged, the unit's `realized` lists
remain empty, and the node records the actual route and source. The construction respects the
paper's derived model and arbitrary cartesian-square base-change clause. Verdict: pass.

Changed during second reading: appended this review only; no Lean code, node, or dependency
changes were necessary.
