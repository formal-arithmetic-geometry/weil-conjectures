## What changed
Added proof-only imports and decomposed the comparison construction into two strictly smaller intermediate theorems. The main theorem now constructs `CupCechResolutionComparison` from the core maps and class-identification data.

## Proved and sorry left
`cupCechFlasqueResolutionComparison` is proved by a real constructor proof. The intermediate declarations `cechFlasqueComparisonCore` and `cechFlasqueComparisonClasses` remain `sorry`, with nodes `lem-sc-cech-flasque-resolution-comparison-core` and `lem-sc-cech-flasque-resolution-comparison-classes`.

## No longer needed
No imports or stated dependencies were pruned; the original module's plan dependencies remain relevant to the intermediate theorem statements.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan requires substantial constructions absent from existing declarations. These were split into two named intermediate results rather than leaving a `sorry` inside the target proof.

## New nodes
`lem-sc-cech-flasque-resolution-comparison-core` and `lem-sc-cech-flasque-resolution-comparison-classes` are new intermediate nodes, each with its own module and declaration.

## Second reading by H4
1. The target statement is byte for byte unchanged; the main proof only assembles the two
   intermediate results.
2. The core node supplies only the comparison maps and quasi-isomorphism, while the classes node
   supplies only the homology identifications and compatibility equations; both are strictly
   smaller and their node signatures match the Lean declarations.
3. All three delivered modules compile with `lcompile.py`; no forbidden declarations occur. The
   only remaining sorry declarations are the two named split nodes.
4. Imports were checked for use: the original public imports remain, and the two added imports are
   proof-only imports for the split declarations. No stated dependency was pruned.
5. The unit route remains through the Cech comparison data and its canonical comparison structure.
   I repaired the split-node metadata and searches and added the missing core proof docstring and
   blueprint tag.
