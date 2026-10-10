Files written:

- `lem-sc-effective-cartier-affine-dimension-drop.json` — statement, split proof; no new nodes, no Mathlib leaf created.
- `citations.json` — verbatim citations for all proof-step dependencies.

Attachments:

- None. I searched `WeilConjectures/` for the item id, its key phrases, and relevant dimension declarations; no matching sorry-free declaration exists.

WANTED:

- None.

What was wrong or incomplete in the input:

- The imported item had no proof steps despite asserting a global affine dimension equality. I supplied the localization argument and recorded the existing local principal-ideal Mathlib leaf and finite-type dimension formula as dependencies.
- The item’s existing Mathlib searches included an unavailable LeanSearch result and a grep query that did not find the relevant declaration. I reran the required searches with the exact item id, including a successful LeanFinder/Loogle search for `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`, and recorded the unavailable service honestly in the inherited search log.

What I could not finish:

- No Lean code is written at stage 1. The global passage from local dimensions to affine Krull dimension is written explicitly via localization and prime correspondence, with the finite-type dimension formula cited; it remains for the stage-2 formalization to instantiate.

## Review by K1

I read the item, its blueprint ancestry (`lem-sc-mult-n-finite-flat`, Tag 0BEV), and the source tags 00KV, 00KW, and 02FX recorded in the item. I also read the complete statements of `def-pc-integral-scheme`, `def-weil-finite-type-morphism`, `lem-weil-pbc-dimension-quotient-nonzerodivisor`, and `lem-kun-dimension-formula`. Step 1 uses only the integral-domain and finite-type hypotheses to establish regularity of the nonzero element, properness of the principal ideal, and Noetherian localizations. Step 2 applies the cited local theorem exactly under its Noetherian-local, maximal-ideal, and nonzerodivisor hypotheses, and spells out the quotient-localization identification. Step 3 uses the cited finite-type dimension formula and states the prime-correspondence/supremum argument needed to pass from all local equalities to the affine equality. I checked the edge cases: `f` nonunit makes the quotient nonzero, while `f=0` and a unit are excluded because the claimed dimension drop would fail there. No source or Lean declaration was silently changed.
## Second reading by K1

- Item statement: checked the integral finite-type affine hypotheses and nonzero nonunit condition against Stacks Tags 00KV, 00KW, and 02FX; zero and unit cases are correctly excluded, and the field case is vacuous.
- Step 1: checked the domain/nonzerodivisor and proper-principal-ideal claims from `def-pc-integral-scheme`; checked Noetherianity through `pqf-lem-locnoeth-lft`; verdict: sound after citation repair.
- Step 2: checked localization, preservation of the nonzerodivisor, and quotient-localization identification against `lem-weil-pbc-dimension-quotient-nonzerodivisor`; verdict: sound.
- Step 3: checked maximal-ideal correspondence and the local-dimension supremum against `lem-pc-scheme-dimension-local-rings`, with `lem-kun-dimension-formula`; the prime-chain reduction to maximal ideals is explicit; verdict: sound after citation repair.
- New nodes: none; B1--B7 are vacuous. Existing-node searches found the needed local quotient and scheme/local-ring dimension results.
- Changes: added `pqf-lem-locnoeth-lft` to step 1 and citations; repaired step 3's unsupported supremum assertion and added `lem-pc-scheme-dimension-local-rings` with its verbatim citation.
