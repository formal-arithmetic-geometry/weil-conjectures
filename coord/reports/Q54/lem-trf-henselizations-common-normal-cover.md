# Stage 1 report: lem-trf-henselizations-common-normal-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-henselizations-common-normal-cover.json` — item, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-normal-polynomial-surjection.json` — new statement node, unsplit; no Mathlib match for the combined arbitrary-variable normality and surjection statement.
- `dag/nodes/sec-trace-formula/lem-trf-henselization-quotient-at-prime.json` — new statement node, unsplit; no Mathlib match.
- `citations.json` — verbatim proof-step citations.

## Attachments

None. I searched the slopmaster2 source for the item id, its key words, and the imported blueprint tags; no sorry-free declaration states the item.

## WANTED

- WANTED: the local archival copy of Huebner--Schmidt, Theorem 6.3 (the online paper was read); it is the source of the surrounding quotient reduction on printed p. 13.

## Not duplicates

- `lem-trf-normal-polynomial-surjection` vs `lem-weil-pbc-polynomial-ring-normal-domain`: the existing node proves normality of a one-variable polynomial ring over a normal domain; the new node additionally gives an arbitrary-variable polynomial ring over `Z` and a surjection onto every commutative ring.
- `lem-trf-normal-polynomial-surjection` vs `def-weil-pbc-mv-polynomial-ring`: the existing node defines the multivariable polynomial ring and its universal property; the new node is the separate existence and normality/surjection assertion.
- `lem-trf-henselization-quotient-at-prime` vs `lem-sbc-strict-henselization-surjective-quotient`: that node concerns algebraic strict henselizations with chosen separable residue fields and an explicit strict-henselization quotient; the new node concerns ordinary henselization of an arbitrary local ring and Tag 05WQ.
- `lem-trf-henselization-quotient-at-prime` vs `lem-sbc-algebraic-strict-henselization-localized-divisor-quotient`: that node specializes to a strict henselization of a localized divisor quotient; the new node is the general ordinary local quotient statement and does not assume a divisor or strict residue field.
- `lem-trf-henselization-quotient-at-prime` vs `lem-trf-henselizations-common-normal-cover` (05WQ): the existing item is the combined common-normal-cover existence theorem, while the new node isolates the ordinary henselization-of-a-quotient lemma used as Step 3 and applies to any local ring and ideal in its maximal ideal.
- `lem-trf-normal-polynomial-surjection` vs `lem-pur-polynomial-field-pid` (030A): the existing node concerns a one-variable polynomial ring over a field and its PID property, while the new node concerns an arbitrary-variable polynomial ring over `Z`, its normal-domain property, and a surjection to every commutative ring.

## What was wrong or corrected

The imported item had no proof steps and cited Tag 05WQ plus a normal-domain presentation without exposing the two non-elementary ingredients. I added statement-only nodes for those ingredients and wrote the four-step quotient reduction. The ordinary henselization notation is kept distinct from strict henselization: no separable-closure or finite-generation hypothesis is introduced. The item statement itself is unchanged.

## Review by Q54

I read the item source description, the proof of Huebner--Schmidt Theorem 6.3 around printed p. 13, Stacks Algebra Tag 05WQ at lines 43616--43624, Tag 00CT on localization of a quotient, and the existing statements of `def-weil-pbc-normal-ring`, `def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-localization-at-prime`, and `def-weil-pbc-henselization-at-prime`. I also read the existing DAG nodes for one-variable polynomial normality and strict-henselization quotient constructions.

Step 1 uses exactly the new normal-polynomial-surjection statement: it supplies `P`, its normal-domain property, and the surjection to `A`. Step 2 uses exactly the existing 00CT node: after setting `q_i=pi^{-1}(p_i)`, its localization map is the quotient localization and is local and surjective; the inverse-image prime and the kernel ideal are the hypotheses needed in the next step. Step 3 uses exactly the new 05WQ node: the kernel ideal lies in the local maximal ideal, so the quotient of the ordinary henselization is the ordinary henselization of `A_{p_i}` and the induced map is local and surjective. Step 4 is elementary functoriality of the quotient and localization maps and records compatibility; it introduces no un-cited theorem.

I checked edge cases including `A=0`, a field with either prime `(0)`, equal primes, and `I=0`: the polynomial presentation and quotient-henselization conclusions remain meaningful, and the two induced maps are still local surjections. Mathlib searches were run and recorded in `searches.jsonl` for both new nodes and for the item; they found no exact theorem. No SGA source is used, no finite-generation hypothesis is added, and no circular dependency is present.
