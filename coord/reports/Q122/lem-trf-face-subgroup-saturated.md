# Worker report: lem-trf-face-subgroup-saturated

## New nodes

- None. The item is split directly; there are no new nodes and no Mathlib leaves.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, the blueprint tag, and face/subgroup/saturated keywords. No sorry-free project declaration states this item exactly. The existing declaration material around `lem-trf-fs-face-sharpening` is not an attachment: it assumes a fine saturated monoid and uses this item as an input, while this item is the general integral saturated lemma.

## WANTED:

None.

## What was wrong and what I changed

The imported item had no proof. I supplied the two-step argument from ILO Expose VIII, 3.1.1--3.1.2. If `ng` lies in `F^{gp}`, write it as `a-b` with `a,b` in `F`, set `h=g+b`, and use saturation to obtain `h` in `Q`; the face condition applied to `nh` then gives `h` in `F`, hence `g` in `F^{gp}`. The final sentence identifies this condition with saturation of the subgroup and torsion-freeness of the quotient. No statement or hypothesis was changed, and no child node is needed because the proof uses only the item's definitions and hypotheses.

I ran the required six Mathlib searches (including a second phrasing for the semantic searches); they found only generic `Subgroup.Saturated`/`AddSubgroup.Saturated` definitions and unrelated subgroup or Grothendieck-group results, so `mathlib_match` remains null. The search commands and their outputs are recorded in `searches.jsonl` and in the item's `mathlib_searches` field.

## Not duplicates

No new node was created. `lem-trf-fs-face-sharpening` is a dependent broader fs statement whose proof cites this item; it is not a duplicate of this general integral saturated subgroup lemma.

## Review by Q122

I read the item node, unit `sk-i-curve-zero`, chapter `sec-trace-formula`, the existing dependency `def-trf-fs-log-blowup`, and the related nodes `lem-trf-fs-face-sharpening` and `lem-trf-face-localization-fs`. The definition node states the group-completion construction and the saturation condition used here; the item's own statement explicitly supplies integrality, saturation, the face condition, and the definition of `F^{gp}`, so the proof steps have no external `uses` and `citations.json` is correctly empty.

Step 1 checks the hypotheses exactly: from `ng ∈ F^{gp}` the subgroup definition gives `a,b ∈ F` with `ng=a-b`; for `h=g+b`, the displayed identity `nh=a+(n−1)b` lies in `F ⊆ Q`, so the item's saturation hypothesis applies. Step 2 checks that `h ∈ Q` makes `(n−1)h ∈ Q`, allowing the face implication to be applied to `nh=h+(n−1)h ∈ F`; subtracting `b ∈ F` then places `g` in `F^{gp}`. The quotient assertion follows directly from the same implication: a positive multiple of a quotient class is zero exactly when the representative's multiple lies in `F^{gp}`. I checked the edge cases `F={0}`, `F=Q`, `n=1`, and `Q=\mathbf N^r` with coordinate faces. The dry-run reviewer initially required steps with no external uses to be marked elementary; I made that mechanical classification explicit after checking that both arguments are direct finite-word deductions from the item definitions and hypotheses. Every proof step is under 2000 characters, and no hidden lemma, duplicate node, unsupported hypothesis, SGA citation, or Lean declaration was introduced.
