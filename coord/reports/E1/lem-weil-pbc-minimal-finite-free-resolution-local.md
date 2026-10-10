# lem-weil-pbc-minimal-finite-free-resolution-local

## Files

- dag/nodes/sec-proper-base-change/lem-weil-pbc-minimal-finite-free-resolution-local.json: split in five steps from Stacks Algebra 0CXF and 00MT.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-free-complex-unit-entry-splits.json: new unsplit statement of Stacks Algebra Tag 00MT, label lemma-add-trivial-complex; no Mathlib match after LeanSearch, Loogle and source grep.

## Attachments

None; the item's Lean audit is none.

## Wanted

None.

## Corrections

The existing node had a correct statement and source but no proof. The source's claim that one can remove trivial summands hides the repeated cancellation and termination argument; the split now gives that argument, including the degree-zero augmentation check. Its prior L review of the statement is preserved.

## Remaining

The new 00MT cancellation node is deliberately unsplit. The configured Mathlib checkout at ~/weil-conjectures-slopmaster2 is unavailable here, so the source grep used the available Mathlib checkout under /home/ubuntu/Poincare-MorganTian/.work/helpers/codex-m47-line/.lake/packages/mathlib/Mathlib. The lead should take that version difference into account when reviewing its search verdict.

## Blueprint and indexing

Searched the whole imported blueprint with blueprint_refs for 0CXF, 00MT, minimal, trivial complex, unit entry, and resolution length; no node states either this item or the 00MT cancellation lemma. The nearest blueprint ancestor is thm-weil-pbc-finite-etale-lifting, whose proof's final sentence asserts essential surjectivity. The new node's via chain starts with this item. For d=1, the cited syzygy node's statement explicitly takes e=0 and gives projectivity of ker(F_0 to M), matching Step 2.

## Review by E1

I read Stacks Algebra 0CXF (lemma-what-kind-of-resolutions-Noetherian-local), 00MT (lemma-add-trivial-complex), and the use of cancellation in 00OA. The item assumes a finite module over a Noetherian local ring and a projective resolution of length at most d, exactly the hypotheses needed for 0CXF's bounded finite-free conclusion. Its additional minimality clause comes from 00MT cancellation. The new 00MT node states the source's direct-sum decomposition for a unit matrix entry, including both rank decreases; it has no proof steps. The DAG, blueprint, Lean and available Mathlib source searches found no exact existing node or declaration.

In Step 1, the d=0 resolution identifies M with a finite projective module; the cited local-freeness node gives a free localization at the maximal ideal, and every element outside that ideal is a unit. In Steps 2-3, the finite-free-resolution node supplies the complex, the cited projective-syzygy statement covers e=d-1 (including d=1, e=0), Noetherian submodule finiteness makes the syzygy finite, and local freeness converts it to finite free. These are the statements of the cited nodes. In Steps 4-5, 00MT gives an identity summand; exactness passes to its complement, while the augmentation kills that summand when i=1 because its degree-zero part is in the differential image. Each cancellation lowers total finite rank by two, so the process terminates; over a local ring every remaining nonunit coefficient lies in the maximal ideal. The d=0 and d=1 cases and zero-rank terms cause no exception. The blueprint ancestor's final sentence is a distant route reference, which the report identifies expressly. I found no A-E defect requiring worker repair.
