Files written:

- `lem-sc-hilbert-denominator-ideal-nowhere-dense` (statement, split; no new nodes)

Attachments: none.

WANTED: none.

The item was not already proved by a declaration in the slopmaster2 source. I searched the source for the item tag and for denominator-ideal and nowhere-dense terminology; no matching project declaration exists. I searched the DAG and blueprint for denominator-ideal and nowhere-dense statements. The neighboring affine denominator-module node is a different statement about a module, and the existing principal-open density node is the needed general tool.

## Review by K1

I read Stacks Project `divisors.tex`, Tag 02P0 (Lemma 31.24.9), including its statement and proof. The item's hypotheses and three conclusions match that lemma, with the total-quotient and regularity meanings written explicitly in the item statement. Step 1 follows the proof's affine localization and line-bundle trivialization: regularity gives a local fraction `a/b` with both entries non-zero-divisors, and the denominator condition is exactly the displayed set. This is an elementary local unpacking of the definitions, so it has no node citation. Step 2 reproduces the proof's two inclusions after clearing a power of `f`; the resulting principal-open section formula is the standard affine characterization of quasi-coherence, and ideal closure is immediate from the defining condition, so this step is marked elementary. Step 3 checks both maps: the first is the subsheaf inclusion, while the second is injective from the stated regularity map. It uses `b in I` and `s(b)=a` to place the two supports inside `V(b)` and `V(a)`, then cites `lem-pc-principal-open-dense-of-nonzerodivisor`, whose statement explicitly says a principal open defined by a non-zero-divisor is topologically dense. Thus the complements are closed nowhere-dense and the local support claims glue. I checked the non-zero-divisor hypotheses are exactly those used by the cited node and tested the affine cases `A = k[t]`, `s = t^{-1}` and `A = k[x,y]/(xy)`, using a non-zero-divisor numerator and denominator. No statement or proof clause was moved into a redundant new node.

What could not be finished: no Lean was written, as required for stage 1; the item remains for later formalization.

## Second reading by K1

- Statement: checked against Stacks `divisors.tex`, Tag 02P0 (label `lemma-regular-meromorphic-ideal-denominators`), lines 6172–6217; all hypotheses and three conclusions match.
- Step 1: checked against Tag 02P0 proof lines 6197–6201; the affine trivialization and non-zero-divisor fraction are justified locally.
- Step 2: checked against Tag 02P0 proof lines 6204–6209; the clearing-power localization argument and ideal closure are valid.
- Step 3: checked against Tag 02P0 proof lines 6212–6217 and the full statement of `lem-pc-principal-open-dense-of-nonzerodivisor`; the support containments in `V(b)` and `V(a)` are correct.
- New nodes: none; the only non-elementary input is the existing principal-open density node, while steps 1–2 are short source-proof unpackings.
- Edge cases: empty spectrum is vacuous; over a field the denominator ideal is the unit ideal; `k[t]` with `s=t^{-1}` gives `I=(t)` and dense `D(t)`; zero-divisor denominators are excluded by the hypotheses.
- Changed `citations.json` to remove a duplicate partial quote; the remaining citation quotes the cited node statement verbatim.
