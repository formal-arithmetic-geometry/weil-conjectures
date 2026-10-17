## What changed

Replaced the proof of `CategoryTheory.derived_exists_perfectSmallClass` with a real
composition of two named intermediate theorems. The target module imports the two
proof-only helper modules and packages their outputs. `DerivedPerfectSmallClassCore`
states the ambient well-generation/cardinal-bound step. `DerivedPerfectSmallClassProperties`
states the formal cardinal-smallness consequences used by the target.

## Proved and sorry left

The target theorem `derived_exists_perfectSmallClass` is proved from the two strictly
smaller intermediate statements. The new theorem
`derived_exists_perfectSmallClass_core` remains `sorry`: its proof is the well-generation
and common regular-cardinal construction from Neeman and Krause. The new theorem
`derived_perfectSmallClass_properties` remains `sorry`: its proof is the filtered
subcoproduct argument from alpha-presentability and Krause Proposition 6.8.1.

## No longer needed

No proof dependency named by the original target node was removed. The original
`lem-grothendieck-derived-has-coproducts` dependency remains needed for the derived
coproduct instance used by the target and both helper statements. No existing module
or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The brief's three proof steps are mathematically appropriate, but the repository had no
Lean declaration for either the well-generation construction or the alpha-presentable
subcoproduct lemma. The available cardinal APIs only provide generic filtered-colimit
factorization and do not construct the required coproduct diagram, so the two missing
steps are split into named statements rather than hidden inside the target proof.

## New nodes

`new-sfb-derived-perfect-small-class-core` records the ambient class, common regular
cardinal, alpha-presentability, and small-coproduct closure statement. Its Lean module
is `lean/Sheaf/CategoryTheory/DerivedPerfectSmallClassCore.lean`.

`new-sfb-derived-perfect-small-class-properties` records the perfectness and bounded
subcoproduct consequences of those hypotheses. Its Lean module is
`lean/Sheaf/CategoryTheory/DerivedPerfectSmallClassProperties.lean`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
