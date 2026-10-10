1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-embedded-points-affine-localization.json`: item split into three proof steps; no new nodes.
- `citations.json`: verbatim citations for the existing affine-removal node.

2. Attachments: none.

3. WANTED: none.

4. The Lean source under `WeilConjectures/` contains no declaration or blueprint tag for this item. The source for Tag 02M7 states the result and explicitly marks its proof as omitted. I therefore supplied the standard agent-written argument: localization of the exact quotient sequence, maximality after localization by clearing denominators, and identification with the quotient constructed on the localized module. No new node was created because these are the proof steps of the item and the only imported non-elementary construction is already stated by `lem-sc-hilbert-embedded-points-affine-removal`.

5. I could not compile Lean by stage-1 rule; no Lean declaration was present to test.

## Review by J1

 I read the item source, Stacks Project Algebra Tag 02M7 (label `algebra-lemma-remove-embedded-primes-localize`), and verified that its hypotheses are exactly a Noetherian ring, a finite module, and an element `f`. I also read the full statement of `lem-sc-hilbert-embedded-points-affine-removal`; it supplies the maximal nowhere-dense-support submodule and the quotient construction used in all three steps. Step 1 uses that maximal submodule and writes out exact localization of `0 -> K -> M -> M' -> 0`. Step 2 uses the same maximality statement while checking support on the principal open and the clearing-denominators argument for a competing localized submodule. Step 3 uses the affine-removal statement's quotient construction and combines it with Step 1. I checked the edge cases `f = 1` (the original quotient is recovered) and `K = 0` (both localized quotients are the localized module). The Mathlib searches were run for the item; associated-prime localization declarations appeared but none states the quotient construction, so the item remains unsplit rather than a Mathlib leaf.

## Second reading by J1

I reread Tag 02M7 (label `algebra-lemma-remove-embedded-primes-localize`) and Tag 02M6 (label `algebra-lemma-remove-embedded-primes`) in the Stacks source. The item statement matches the source hypotheses and conclusion; the existing affine-removal node supplies the quotient construction. Step 1 was checked against exact localization of the defining short exact sequence. Step 2 was checked component by component on `D(f)`, including the necessary removal of primary components contained in `V(f)`; the earlier denominator-clearing wording was repaired. Step 3 was checked against the definition of the localized quotient and the isomorphism from Step 1. No new node was created, so B1-B7 and duplicate-node checks are vacuous. I tested `f = 1`, `f = 0`, the zero module, and a field; all give the stated identification. I corrected the source metadata to name Tag 02M7 without the inconsistent lemma-number citation and expanded Step 2 to avoid the unsupported claim that arbitrary denominator clearing preserves nowhere-dense support.
