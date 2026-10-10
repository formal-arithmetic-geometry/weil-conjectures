1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-picard-h1-restriction-compatibility.json`: statement node, split; no Mathlib leaf.
- `citations.json`: six verbatim step-to-node citations.

2. Attachments: none.

3. WANTED: none.

4. What was checked and changed:

- The item statement was checked against `/home/ubuntu/c1-stacks-review/varieties.tex`, Lemma `09NY`, together with Cohomology Lemma `02UV` and Lemma `09NU`. Its hypotheses and conclusion are unchanged.
- I searched the whole DAG and the slopmaster2 Lean source for the item tag and for Picard/H^1 restriction declarations. No exact sorry-free declaration exists, and no existing node states this naturality result separately.
- Step 1 uses the statement of `thm-sc-hilbert-90`, which explicitly sends an invertible module to its Zariski Isom torsor. This is the non-elementary Hilbert-90 input.
- Step 2 uses the stated pullback functor from `def-pc-module-pullback` and the Isom-torsor description in `thm-sc-hilbert-90`; the identification of pulled-back transition maps and actions is a direct sheaf calculation, so it is marked elementary. This is the precise naturality assertion that the imported item had left as an unsplit proof obligation.
- Step 3 uses the natural closed-immersion cohomology isomorphism in `lem-sc-cohomology-closed-immersion-pushforward` at `p=1`, then applies the Hilbert-90 identification on `Z`.
- `citations.json` was written only with verbatim substrings of the cited node statements. No new node was created because every non-elementary input already exists in the DAG.
- Small cases checked: `Z=X` and `i=id` give identity maps; for `Z=\varnothing`, both restriction and the target cohomology class are trivial; for a reduced point `Z`, the statement specializes to the usual restriction of a line-bundle transition cocycle to the point.

## Review by C1

I read the item source at Lemma 09NY in `varieties.tex` and the cited 02UV and 09NU statements in the Stacks review files. I also opened the statements of `thm-sc-hilbert-90`, `def-pc-module-pullback`, and `lem-sc-cohomology-closed-immersion-pushforward`; each says exactly the fact quoted in `citations.json`. Step 1 uses the Hilbert-90 torsor classification, step 2 uses pullback functoriality and performs the elementary transition-function calculation, and step 3 uses the natural H^1 pushforward comparison and Hilbert-90 on the closed subscheme. The closed-immersion hypothesis is used in step 3, while the module pullback and units actions are checked in step 2. I corrected the imported empty proof by making the naturality calculation explicit and by recording the exact statement quotes. No new statement, Mathlib leaf, attachment, or tool-use declaration was required.

5. What could not be finished: nothing.
