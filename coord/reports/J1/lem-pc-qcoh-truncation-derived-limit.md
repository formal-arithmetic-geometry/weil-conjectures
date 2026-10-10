# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-qcoh-truncation-derived-limit.json`: item split into three proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited dependency of every step.

## Attachments

None. No sorry-free project declaration states this item exactly.

## WANTED

WANTED: `literature/stacks-project/perfect.tex`, Tag 08D4 (including Tags 08D3 and 08D1), for the truncation tower and derived-functor comparison.

## Not duplicates

No new nodes were created, so there are no duplicate pairs.

## What was checked

The item was compared with the imported source citation (Stacks Tag 08D4, with the supporting Tags 08D3 and 08D1 named by the node). The Lean source tree was searched for the item id, its key notions, and the blueprint tag; no declaration under `WeilConjectures/` states the item. The existing nearby nodes were read, especially the standard truncation definition, the Roos derived-limit definition, and the left-exact additive derived-functor definition.

## Review by J1

Step 1 uses only the standard truncation triangle and the Roos definition. It explicitly introduces the tower and checks degreewise eventual constancy before invoking the cited Stacks truncation-tower result. Step 2 uses the definition of a right derived functor and the Roos definition; it checks the product-preservation hypothesis on `F` and explains how the K-injective computation gives a morphism of Roos triangles. Step 3 uses the same three definitions and records that the canonical maps are natural. The hypotheses that `X` is a scheme, `E` is in the quasi-coherent derived category, and `F` is additive, countable-product preserving, and has `RF` are all retained from the item statement. No new statement was introduced, so there was no additional small-case lemma to test; the edge case `E=0` is immediate from the same tower and all maps are zero.

The Mathlib searches were rerun with the item id using LeanFinder, Loogle, grep, and LeanSearch. LeanFinder returned only generic truncation/derived-category declarations; Loogle and grep found no derived-limit theorem; LeanSearch reported an unavailable service and is recorded as such in the node.

## What was wrong or incomplete

The imported node had no proof, stale Mathlib search records, no Lean audit field, and no split report. These were repaired. The referenced Stacks PDF is not present in this checkout, so the source was recorded as WANTED rather than downloaded.

## What could not be finished

No Lean compilation is permitted in stage 1. The split is left for the second worker to review and deliver after the required dry run.

## Second reading by J1

- Item statement: checked against Stacks Tag 08D4, label `lemma-nice-K-injective`, and the derived-functor comparison in Tag 08U1, label `lemma-RF-commutes-with-Rlim`; the two asserted isomorphisms and all hypotheses agree.
- Step 1: checked against the standard truncation definition and the Tag 08D4 truncation reconstruction argument; the degreewise stabilization and derived-limit conclusion use the cited statements.
- Step 2: checked against Tag 08U1 and the new comparison node; the product-preserving right-derived-functor hypothesis is applied exactly, with no unsupported Roos five-lemma argument.
- Step 3: checked against the truncation, derived-limit, and Tag 08U1 comparison statements; naturality of the canonical maps is elementary from those constructions.
- New node `lem-pc-derived-functor-commutes-derived-limit`: statement-only, self-contained for schemes and module sheaves, sourced to Tag 08U1 / `lemma-RF-commutes-with-Rlim`; its three recorded Mathlib searches ran and found no matching theorem, and blueprint search found no duplicate.

Changes made: added the missing Tag 08U1 comparison node; corrected the item and Step 2 source references; replaced the unsupported K-injective/Roos five-lemma prose with a direct cited application; added the corresponding citations and Step 3 dependency.
