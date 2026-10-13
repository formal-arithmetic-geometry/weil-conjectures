## What changed

Removed the two disputed torsion-coefficient instances and corrected their module documentation; imports are unchanged against sheaf-dag. The
bounded-below torsion-coefficient instance was removed because its statement is false for
arbitrary compactifiable morphisms: disconnected schemes can have unbounded fibre dimensions.
The remaining bounded-below APIs now require callers to supply the corresponding
`HasBoundedBelowUpperShriek` or `HasBoundedBelowUpperShrieks` hypothesis.

## Proved and sorry left

No `sorry` remains in the delivered module. The false declaration
`hasBoundedBelowUpperShriek` and its global wrapper instance `hasBoundedBelowUpperShrieks` were
removed; no theorem is proved from the disputed strictification statements.

## No longer needed

The two disputed torsion-coefficient instances are removed. The strictification imports and contradiction theorem belonged to the earlier returned delivery and are absent from the base; this delivery changes no imports or DAG dependencies.

## Where the brief, the DAG or earlier work was wrong

The previous delivery used an ex-falso proof from the explicitly disputed
`exists_site_system_strictification_data`. The bounded-below assertion is false without a
uniform finite cohomological-amplitude hypothesis, so that contradiction route was invalid.

## New nodes

None.

## Forced adaptations

None.

## Earlier second reading (a previous round; superseded)

1. Removed both strictification imports and the private contradiction theorem.
2. Compiled the repaired module successfully with `lcompile.py`.
3. Confirmed no `sorry`, `axiom`, or unsafe declaration was introduced.
4. The change record `coord/changes/hasBoundedBelowUpperShriek.md` documents the removed false instances and their users.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered module with the repository version. Existing declaration signatures
   that remain are byte-for-byte unchanged; the two disputed torsion-coefficient instances are intentionally removed and documented by the change record.
   Verdict: the interface change is explicit and mathematically motivated.
2. I compiled the module with `lcompile.py`; it succeeds with no warnings. The module contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The remaining declarations
   use only the permitted ambient assumptions.
3. The removed bounded-below instances were false for compactifiable morphisms with disconnected
   schemes and unbounded fibre dimensions. The remaining classes are explicit hypotheses, so no
   new theorem is split off and no new node is needed.
4. The proof uses the existing adjunction construction and its `IsLeftAdjoint` dependency. The
   strictification imports and contradiction route are absent; no further proof-only import is
   needed. The unit route for the upper-shriek definition and adjunction is preserved.
5. The DAG declarations for the module continue to match the Lean declarations used here. The
   change record names the removed declarations and their downstream adaptation requirement.

I also corrected stale module documentation that still claimed a torsion-coefficient bounded-below
instance existed; no mathematical declaration was changed by that documentation repair.

## Second reading by P3

1. I compared the delivered module with the repository version. The surviving declaration
   signatures and definitions are unchanged byte-for-byte. The two removed torsion-coefficient
   instances are an intentional interface repair recorded in
   `coord/changes/hasBoundedBelowUpperShriek.md`; downstream users retain explicit hypotheses.
   Verdict: the visible change is documented and mathematically necessary.
2. I compiled `UpperShriek.lean` with `lcompile.py`; it succeeds without warnings. There are no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the
   delivered module. Its declarations use only permitted ambient axioms.
3. No statement was split off and no new node was added. The retained bounded-below classes are
   true hypotheses, while the removed global instances were false for disconnected schemes with
   unbounded fibre dimensions. The change therefore does not weaken a theorem used downstream.
4. Imports are unchanged because the proof and definitions still use the same lower-shriek and
   derived-adjunction declarations. The unit route through the derived lower-shriek adjunction
   and chosen right adjoint is preserved.
5. The module's DAG route remains consistent: the adjunction instance and upper-shriek definitions
   are unchanged, and the removed disputed instances have no corresponding proof dependency.

I changed only the stale bounded-below documentation and removed the two false torsion-coefficient
instances, with the associated change record; no imports, proofs, or DAG nodes required repair.
