# Stage 1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-proper-open-p-proper.json`: item converted to a Mathlib leaf; no new nodes.
- `citations.json`: empty because the Mathlib leaf has no proof steps.

## Attachments

None.

## WANTED

None.

## What was checked

The item source is the blueprint node `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/lem-weil-pbc-proper-open-p-proper.md`, whose sole argument identifies p as the base change projection of u and invokes proper base change and proper-implies-separated. The existing statement dependency `def-weil-pbc-proper-open-comparison` explicitly constructs the cartesian square and names p as its projection. The existing `lem-weil-pbc-proper-base-change` is itself a Mathlib leaf, but the present item is directly covered by Mathlib's pullback instance.

I read Mathlib `AlgebraicGeometry/Morphisms/Proper.lean`: `IsProper.instSndScheme` (line 83) gives `IsProper (Limits.pullback.snd u j₂)` from `IsProper u`, exactly the morphism p. The `IsProper` class declaration (line 42) extends `IsSeparated`, supplying the conclusion that p is separated. The hypotheses match the item: u is proper, j₂ is arbitrary (in particular an open immersion), and V is the fibre product. I tested the orientation on the identity/open special case: when u is an identity, p is the identity on X, and the instance still applies.

The required searches were run with `msearch.py`: LeanFinder found `instSndScheme`; grep found the exact instance at line 83; Loogle returned no hits because its query parser did not recognize `IsProper`; LeanSearch was unavailable and is recorded as such. Blueprint search found no alternate node statement. No source or statement correction was needed.

## Review by NI

I checked the item against the cited blueprint paragraph and the full statements of both dependencies. The only proof step is precisely the Mathlib instance application, so there are no node citations to quote and `citations.json` is empty. The comparison node supplies the cartesian square and the named projection; the base-change node independently states the same general stability fact. Mathlib's class hierarchy supplies separatedness without adding a hypothesis. The edge case u = id confirms the projection orientation. The item has no Lean declaration in the reference source, and no new node was created.

## What was wrong in the imported node

It was marked `imported` despite being an exact Mathlib leaf. Its proof paragraph duplicated the existing Mathlib base-change theorem and the `IsProper` superclass implication. I changed only the split-owned fields to record the Mathlib match and removed the proof steps.

## What could not be finished

Nothing.

The literature check also read Stacks `morphisms.tex`, Tag 01W4 (`lemma-base-change-proper`) and Tag 01W1 (`definition-proper`): the former states stability under arbitrary base change, and the latter includes separatedness in properness. The Mathlib convention uses locally finite type rather than finite type in its class, but `UniversallyClosed.lean:167` supplies quasi-compactness, so these conventions agree. The first preflight required retaining a non-null literature `proof_origin` even for a leaf; this was repaired by recording Tags 01W4 and 01W1. No mathematical repair was required.

## Second reading by NI

- Item statement: checked every hypothesis and conclusion against the blueprint node and Stacks Tags 01W4 and 01W1; the proper base-change projection and separatedness clause agree, including the arbitrary open immersion case.
- Proof steps: there are no proof steps because the item is a Mathlib leaf; the recorded Mathlib instance has the exact pullback projection orientation, and `IsProper` supplies separatedness.
- New nodes: none; there are no B1–B7 obligations or new-node searches to audit.
- Changed nothing: the worker's Mathlib leaf conversion, source provenance, searches, and report review are accurate and the dry-run preflight passed.
