## What changed

Split the chain-level construction into two named intermediate theorems and combined them in the target theorem. The construction and compatibility components remain explicit public statements with documented blueprint nodes.

## Proved and sorry left

The target theorem is reduced to the two named components. The remaining named holes are `AlgebraicGeometry.singleComplexOpenComparison_union_ses_objects` and `AlgebraicGeometry.singleComplexOpenComparison_union_ses_compatibility`.

## No longer needed

No imports or existing DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires substantial K-injective and cylinder constructions; these were isolated into construction and compatibility components so the target proof is a complete composition of strictly smaller statements.

## New nodes

`new-single-complex-open-union-ses-objects` and `new-single-complex-open-union-ses-compatibility`.

## Second reading by S4

1. Compared the delivered presentation module with the repository version. The target signature is byte-for-byte unchanged; only its proof and the two explicitly declared component imports differ.
2. Compiled all three sandbox modules with `lcompile.py`; they compile without errors. The two component theorems remain the named, documented `sorry` holes and no definition contains `sorry`.
3. Checked the split statements against their Lean declarations and repaired the DAG metadata, including exact signatures, proof steps, blueprint, searches, and module paths. Both statements are the needed construction and compatibility components and are strictly smaller than the target.
4. Checked the proof route: the target applies the construction component and then compatibility, preserving the unit's short-exact presentation route. No imports were found removable.
5. The DAG nodes now agree with the declarations and record the postponed source arguments. The remaining holes are `AlgebraicGeometry.singleComplexOpenComparison_union_ses_objects` and `AlgebraicGeometry.singleComplexOpenComparison_union_ses_compatibility`; no additional holes were introduced.

I repaired the two node records, corrected their module names and exact signatures, added the required proof metadata and documented proof sketches to the split theorems, and added this second-reading report.
