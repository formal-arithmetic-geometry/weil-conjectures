## What changed

Replaced the hole in AlgebraicGeometry.formalFunctions_degreeZero_augmented_sections
by the three-step argument of its node. Constructed restricted injective resolutions
and compatible open choices locally without flatness. Proved that degree-zero
cohomology restriction to a whole open is injective from the canonical augmentation
square. Applied the theta predicate to an augmented section, identified its germ,
and cancelled restriction. Added proof-only imports for the restriction theorem,
the degree-zero cohomology-map comparison, and two smaller comparison modules.

Repaired the saved attempt's compile timeout by using the project's relaxed
transparency settings for the main theorem and explicitly unfolding the
global-sections functors when supplying their finite-limit instances. The
instances are the named Mathlib evaluation instances; this avoids an expensive
implicit conversion. No file or proof was split to repair compilation.
Removed the stale second-reading section: the changed proof needs a new reader.

## Proved and sorry left

Closed: AlgebraicGeometry.formalFunctions_degreeZero_augmented_sections (one original
hole), by decomposition. Added two holes, each a named public theorem in its own module:

- AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_zero_augmentation:
  lem-weil-pbc-resolution-section-class-zero-augmentation; the normalization of the
  canonical section-class comparison on augmented sections, before taking germs.
- AlgebraicGeometry.Scheme.Modules.tensorUnit_open_degree_zero:
  lem-weil-pbc-tensor-unit-open-degree-zero; the restricted tensor-unit augmentation
  square, independently of theta and stalks.

The item's module has no remaining sorry. Its private helpers are proved.
This is a decomposition (one hole closed, two added), not a sorry-free proof of the
underlying mathematics. Neither lower statement repackages the original conclusion:
one concerns the source section class, the other the target cohomology square.

## No longer needed

No existing import was removed: the sole public import FormalFibreCohomology is
needed by the statement. No module is claimed pruned from the targets' import closure.
The main node no longer directly invokes lem-weil-pbc-higher-direct-image-presheaf
(Sheaf.Paper.HigherDirectImagePresheaf); the source normalization node retains it as
an ingredient. FlatBaseChangeOpenChoicesExist is not imported: its existence proof
has unused flatness hypotheses, and our private construction uses restriction
injectivity directly without those assumptions. No unit statement or realized step
was bypassed. The second reader replaced the proof-only import of
ModuleCohomologyFMapZeroAugmentation with BasicPropertiesDegreeZero. The main node
no longer directly uses lem-weil-pbc-module-cohomology-fmap-zero-augmentation or
lem-weil-pbc-left-exact-injective-resolution-degree-zero; those are retained
through the existing degree-zero comparison (and the former in the tensor-unit
split-off). This changes direct dependencies only, not the import closure.

## Where the brief, the DAG or earlier work was wrong

The previous delivery timed out at the 60-second local compile limit. Profiling
identified expensive global-sections/evaluation conversion in the whole-open
injectivity helper. Targeted unfolding and explicit instance terms repaired this
without changing a definition, theorem signature or time limit. The repaired
module compiled cleanly in 53.3 seconds in the direct local check. Diagnostic
options and unsuccessful experiments were removed before the delivery check.

The original plan is mathematically applicable, but the existing higher-direct-image
presheaf theorem does not state the augmentation normalization needed in its second
step, and the flat-base-change choice existence theorem requires flatness even though
its implementation does not use it. Both facts were checked in source. The main
module's sole initial import supplied definitions but not those two comparison
identities. The copied private choice construction removes only unused flatness
assumptions; it chooses no data from an unproved mere existence theorem.

New statements were checked on the empty open/fibre, the zero module and zero
sections: the canonical augmentation identities and unit square apply unchanged.
All morphisms, augmentations, and section identifications remain the fixed ones.
Read Stacks Tags 01E4 and 01FB online; the repository literature directory holds
lists rather than the source text. Mathlib searches used LeanFinder, Loogle, grep,
and LeanSearch (the latter returned HTTP 500 and is recorded unavailable).
The inherited blueprint ancestor lookup returns None because created.item records
module names; the new nodes preserve that reported ancestor and record their exact
parent proof steps. Blueprint-wide searches for section class, tensor unit, 01E4,
01FB and formal functions found no duplicate of either new statement.

## New nodes

lem-weil-pbc-resolution-section-class-zero-augmentation is stated in
Sheaf.AlgebraicGeometry.ResolutionSectionClassZeroAugmentation. It isolates the
canonical degree-zero section-class normalization in Step 2, without germs or theta.

lem-weil-pbc-tensor-unit-open-degree-zero is stated in
Sheaf.AlgebraicGeometry.TensorUnitOpenDegreeZero. It isolates the tensor-unit and
restriction augmentation comparison in Step 3, without germs or theta. Its source
is the degree-zero calculation of the fixed unit square and Stacks 01FB.

No existing definition, signature, visibility or target statement changed. No forced
adaptations or change records are needed.

## Second reading by D2

1. **Visible declarations.** I diffed the delivered main module against the repository version. The target theorem signature is byte-for-byte unchanged; the delivery adds only proof-only imports and private helpers, plus the two new split-off theorem modules. The DAG updates alter proof routes and dependencies only.

2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`; each compiled without errors. The main target has no `sorry`; the two documented split-off theorems retain their named `sorry`s. An axiom probe reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from those split-off theorems. No forbidden declarations or hollow definitions occur.

3. **Statements and split-offs.** I checked both new statements against their uses of `RestrictedResolutionSections`, `FlatBaseChangeOpenChoices`, and `ModuleCohomologyFMapData.map_zero_augmentation`, and tested the stated empty-open, zero-module, and zero-section edge cases described in the report. Each is strictly smaller than the target: one normalizes a source section class and the other proves the restricted tensor-unit square. Searches over the library and the recorded Mathlib searches found no duplicate declarations.

4. **Route and pruning.** The main proof follows the unit route: restricted injective resolutions and open choices, source section-class normalization, theta and tensor-unit comparison, then injectivity of whole-open degree-zero restriction. The proof-only imports are all used. The DAG `proof` and `proof_deps` match the code; no unit step is bypassed. The old higher-direct-image and flat-base-change existence ingredients are retained only through the split-off/source construction as recorded.

5. **Definitions and interfaces.** No existing definition, public visibility, or target/interface statement changed. The explicit constructions use fixed adjunction units and canonical restriction maps; no data is chosen from a mere unproved existence proposition. The unit record remains unchanged.

The actual delivery's compile hit the 60-second limit after the successful dry run.
I repaired the whole-open injectivity helper by using the existing
`moduleCohomologyFMap_basic_degree_zero` comparison, replacing its explicit
augmentation-square/finite-limit instance construction. Its proof-only import is
now `BasicPropertiesDegreeZero`; the main node now records that theorem in its
third step and dependencies. I also made the locally chosen resolutions `have`
bindings rather than reducible `let` bindings, avoiding unnecessary unfolding.
I removed redundant unfolding of xi, applied the injectivity theorem first,
and composed the final equalities directly with an expected type. The final
three-module compilation passed; the revised main module compiled in 52.0 seconds. Existing signatures and
all new statements are unchanged; no extra holes were added.

The main node no longer directly uses
`lem-weil-pbc-module-cohomology-fmap-zero-augmentation` or
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`: both remain ingredients
of the proved degree-zero comparison, and the first remains in the tensor-unit
split-off. This changes direct dependencies only; no module is claimed pruned.
