## What changed

Rebased the delivered proof onto the current repository version of
`Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup`, as required by the return.
The current version retains the public `picardScalarCech_externalCup_core` interface;
that visibility is preserved.  The fixed-degree intermediate theorem
`picardScalarCech_externalCup_pointwise` remains the only unresolved compatibility
step.  The public core theorem is proved by applying it, and the original upper
 theorem is proved by applying the public core theorem.

## Proved and sorry left

`picardScalarCech_externalCup_core` and `picardScalarCech_externalCup` are proved.
The remaining sorry is `picardScalarCech_externalCup_pointwise`, recorded by the
new node `lem-sc-picard-scalar-cech-external-cup-pointwise`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was based on commit `0040afc0e`, while the module had since
changed on `sheaf-dag`.  In particular, the current module's core theorem is public;
the repaired file preserves that signature and visibility while reapplying the
same pointwise decomposition.

## New nodes

`lem-sc-picard-scalar-cech-external-cup-pointwise` records the fixed-degree scalar
Cech external-cup compatibility used by the core theorem.

## Second reading by J1

1. Compared the delivered module with the repository version. Existing theorem
   signatures and visibility are unchanged; the only additions are the named
   pointwise split theorem and proof applications.
2. Compiled the module with `lcompile.py`; it succeeds. The only remaining `sorry`
   is the named pointwise theorem, with no forbidden declarations or hollow
   definitions.
3. Checked the split statement against its fixed-degree specialization and the
   core statement. It is true as the required strictly simpler reduction, has a
   source docstring, and has the matching DAG node; no duplicate declaration was
   found in the library.
4. The proof uses the existing component and comparison imports and preserves the
   unit route. The pointwise theorem is the sole unresolved compatibility step;
   no imports or proof dependencies were pruned.
5. The DAG node's statement, proof steps, dependencies, origin, and Lean
   declaration agree with the module. No statement change or forced adaptation
   is present.

Changed only this report section during second reading; no Lean proof repair was
needed.
