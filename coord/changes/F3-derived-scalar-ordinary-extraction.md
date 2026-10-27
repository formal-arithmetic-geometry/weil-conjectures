# F3: extract the already proved ordinary scalar comparison

The item `Sheaf.Paper.DerivedScalarMateData` exceeds the 60-second file limit when
the ordinary construction and the derived proof are checked together. Profiling
identified repeated component-conversion checks. First replace those conversions
by explicit equations and isolate the fixed-representative comparison behind a
private definition and its component lemma. Then extract the self-contained ordinary
part to the new module `Sheaf.Paper.DerivedScalarTensorOrdinary`.

The nine public declarations from `restriction` through `ordinaryComplexIso`,
including `ordinaryTensorIso_existsUnique`, retain their full names, signatures,
visibility, attributes and definition bodies. The original item publicly imports
the new module and keeps every original public import. Only private proof helpers
and theorem proofs are adjusted. No other existing Lean module is changed.

The new DAG node `lem-sfb-scalar-tensor-ordinary-normalization` records the extracted
ordinary theorem. Its attachment lists the nine moved declarations; the original
node retains the remaining declarations and depends on the new node. No target
statement or mathematical definition changes. Since the exported declarations and
their unfolding behavior are unchanged, this extraction forces no consumer edits.

Validation: compile all four sandbox modules in import order using `lcompile.py --all`,
then run the required delivery preflight.

The representative construction is also fully proved in the new module
`Sheaf.Paper.DerivedScalarTensorRepresentatives`. Its one public theorem
`representativeScalarTensorIso` constructs the natural comparison only on flat
K-flat representatives, with the original normalization. It introduces no holes.
The assigned theorem descends it by fully faithful restriction and proves
uniqueness by cancellation. This isolates the construction from the descent proof
after the first extraction alone was still over the file limit.

Finally isolate the fully proved fixed-coefficient tensor calculation in
`Sheaf.Paper.DerivedFixedCoefficientTensorComparison`, with theorem
`fixedCoefficientTensorIso`. Its normalization holds for every map from a flat
K-flat representative. The scalar representative theorem composes this result
with the existing scalar counit and ordinary comparison. This further extraction
follows a representative-file timing failure after optimizing the component API.
No unresolved statements are introduced by any extraction.

All four delivery modules compile. The three direct consumers
`DerivedScalarMateExactStructures`, `DerivedScalarMateProjectionNormalization`,
and `DerivedScalarMateThickLocus` also compile unchanged against the new modules.
Their temporary sandbox copies were removed after verification. No consumer
adaptation was necessary.
