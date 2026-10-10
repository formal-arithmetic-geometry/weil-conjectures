# lem-weil-pbc-coherent-artin-rees

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-artin-rees.json`: split into four proof steps using the existing Mathlib leaf `lem-weil-pbc-artin-rees` and existing affine quasi-coherent module nodes. No new node, no Lean edit.

## Attachments

None. I searched the slopmaster2 source at `71d63dcf` by the item ID, `ArtinRees`, `artin_rees`, `Artin-Rees`, `coherent` with `Rees`, and `exists_pow_inf_eq_pow_smul`, checked `dag/lean_names_upstream.json`, and searched `local/sorry_map_slopmaster2_full.jsonl.gz`. No declaration states the sheaf-level assertion. The sole occurrence of Mathlib's module Artin-Rees in that source is a use in `WeilConjectures/Mathlib/RingTheory/Filtration.lean:496`, not a sheaf theorem.

## WANTED

None.

## Source and blueprint

I read `/tmp/stacks-project/coherent.tex:2584-2605`, where `lemma-Artin-Rees` says exactly the equality for a coherent module, quasi-coherent submodule, and quasi-coherent ideal on a Noetherian scheme, and reduces the proof to a finite affine cover. `/tmp/stacks-project/tags/tags:2549` identifies it as 01YA. I read `/tmp/stacks-project/algebra.tex:12186-12219` for the module equality of 00IN and verified its label in `tags/tags:685`. The item's extra inclusion follows from the equality and the submodule inclusion. The source hypotheses and the item's hypotheses agree; its statement remained unchanged.

The nearest blueprint ancestor is `thm-weil-pbc-finite-etale-lifting` (`tools/blueprint_refs.py ancestor`). The existing `blueprint.from.place` names its step 7 (0GS2 essential surjectivity) and the route through `lem-weil-pbc-coherent-homs-over-open` to 01YB's uses of 01YA; the split report now names those places. Whole-blueprint searches `blueprint_refs.py search Artin-Rees`, `search 01YA`, and `search coherent modules` found no blueprint theorem asserting this sheaf-level Artin-Rees lemma, so the existing `same_as: []` is correct. No new node was made.

## B-E self-check

- B1-B8: no new nodes. The item retains its self-contained statement, its definition citations, and the verified Stacks tag/label; the Mathlib leaf `lem-weil-pbc-artin-rees` names `Ideal.exists_pow_inf_eq_pow_smul` in `Mathlib/RingTheory/Filtration.lean:389` with the exact module equality and the line checked by its earlier review. B9 and B10 are addressed above.
- C1-C8: step 1 uses the public finite-type and ideal-product statements; step 2 uses precisely the equality in the public module Artin-Rees node; step 3 uses the public cokernel and kernel statements to make the intersection quasi-coherent and calculate it on affine opens; step 4 cites preservation of quasi-coherence under restriction and the affine tilde/global-sections equivalence to identify subsheaves. The finite subcover, maximum of finitely many constants, ideal-power arithmetic, and checking equality on an open cover are expanded in the steps. No unstated external theorem, other-unit tool, or new citation cycle is introduced.
- D1-D5: this is the proof of the existing sheaf claim, not a restatement in a child. The previously implicit sheaf intersection identification is made explicit as a kernel.
- E1-E6: each affine coordinate ring is Noetherian by the locally Noetherian cover; `M_i` is finite because `F` is coherent and `N_i` is finite because a quasi-coherent submodule of coherent `F` is coherent on this locally Noetherian scheme. Step 2 explicitly proves that enlarging a local Artin-Rees bound preserves the equality. Step 3 checks that both sides are quasi-coherent before using affine sections. Small cases checked: empty scheme (empty cover, `c=0`), zero ideal, unit ideal, zero submodule, `c_i=0`, and `n=c`.

## Verification and outstanding work

- `python3 tools/review_split.py lem-weil-pbc-coherent-artin-rees`: PASS, 0 new nodes.
- `python3 tools/blueprint_refs.py check lem-weil-pbc-coherent-artin-rees`: 0 field errors.
- `python3 tools/check_dag.py --cycles`: 0 cycles and 0 self-loops; exit 1 on seven pre-existing reachability errors (`constructible-finite-pushforward-approximation`, `constructible-finite-pushforward-noetherian`, `constructible-approximation`, `finite-cover-killing`, `finite-stage-killing`, `prime-torsion-devissage`, `pushout-monicity`). None is this item or a node it adds.
- `git diff --check`: PASS.

No source, blueprint, or brief error requiring a statement change was found. The seven base reachability errors are outside this claim. No unresolved proof step or new node remains from this split.

## Review by F1

I read Stacks Cohomology of Schemes 01YA (`lemma-Artin-Rees`, `coherent.tex` lines 2584-2605) and its cited Algebra 00IN. The item's Noetherian scheme, coherent F, quasi-coherent submodule G and ideal I, and eventual equality match the source hypothesis by hypothesis; the stated inclusion follows from that equality. There are no new nodes. The worker's whole-blueprint search found no same statement, the existing ancestor/via route identifies the 01YA use in 01YB, and the B10 done-branch search found no sheaf-level Lean declaration (B1-B10).

Step 1 obtains a finite affine Noetherian cover from the cited definitions and uses `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` (2) plus `lem-weil-pbc-quasi-coherent-finite-type-affine` (a) to make both affine modules finite. The ideal-product node supplies their affine sections. Step 2 applies the exact 00IN equality in `lem-weil-pbc-artin-rees` on each affine and explicitly proves that replacing each bound by the finite maximum preserves equality. Step 3 uses the cited quasi-coherent cokernel and kernel nodes to express the intersection as a kernel with the required affine sections. Step 4 uses the public restriction and affine tilde/Gamma statements to promote equal affine sections to equal subsheaves, and the product definition gives the final inclusion. The remaining finite-cover and ideal-power calculations are elementary; no proof internals or unrelated unit route are assumed (C1-C8, D1-D5).

I checked the empty scheme (c=0), zero and unit ideals, zero G, and n=c. No ideal is assumed finite type separately, and the Artin-Rees leaf is applied only after its Noetherian and finite-module hypotheses are established. The worker tightened step 4 to cite quasi-coherence under restriction before this review; no further correction was needed. `review_split.py` passes and the cycle check has no cycle; seven unrelated reachability warnings remain (E1-E6, A, F).
