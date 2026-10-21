# Worker report: lem-sfb-countable-normed-orthogonal-basis

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-countable-normed-orthogonal-basis.json` — existing item split into four proof steps; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-ultrametric-best-approximation.json` — new statement-only auxiliary node; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ultrametric-orthogonal-extension.json` — new statement-only auxiliary node; no Mathlib match.
- `citations.json` — two entries, one for each cited node use, with verbatim statement quotes.
- `report.md` — this report. `searches.jsonl` contains the required msearch records.

New nodes: 2. New Mathlib leaves: 0.

## Attachments

None. I searched `WeilConjectures/` for the item id, its title and the notions of countable normed ultrametric spaces and orthogonal bases, including the slopmaster2 checkout. No project declaration states the item exactly; no declaration with the blueprint tag exists. The Mathlib hits are finite-dimensional real/complex projection, generic finite-dimensional completeness, or basis-extension APIs with different hypotheses, so this is not an attachment or Mathlib leaf.

## WANTED:

- WANTED: an exact external reference for nearest-point attainment in a finite-dimensional subspace of a discretely valued ultrametric normed space, for `lem-sfb-finite-ultrametric-best-approximation`.
- WANTED: an exact external reference for the residual orthogonal-extension lemma, for `lem-sfb-ultrametric-orthogonal-extension`.

## Problems corrected

The imported item had no proof and an empty split. I kept its statement, hypotheses, finite/countable index alternatives, prescribed first vector, finite-support interpretation, and continuity conclusions. The blueprint source is an agent auxiliary paragraph and explicitly says the finite-dimensional best-approximation reference is WANTED. I made the two hidden lemmas explicit instead of hiding them inside the induction: nearest-point attainment and adjoining a residual orthogonal vector. The final normalization, uniform constants, coefficient estimates, and continuity bounds remain direct steps of the item. No completeness of `V` and no infinite-series interpretation is added.

The full DAG and blueprint were searched for orthogonal-basis, ultrametric-basis, nearest-point and relevant declaration phrases; no duplicate or same-as blueprint node was found. The msearch results were read. `leanfinder`, `leansearch` and source grep find only unrelated real/complex or generic results; the two Loogle patterns were rejected as unknown identifiers, recorded honestly with an unavailable-pattern verdict. The item’s pre-existing Mathlib searches were also read and support the no-match conclusion.

## Unfinished work

None for this one-level stage-1 split. The two new statement-only nodes remain ordinary downstream queue items. No Lean was written, and no compiler, Lake, local `check_dag.py`, `review_split.py` or preflight was run.

## Not duplicates

`lem-sfb-finite-ultrametric-best-approximation` vs existing finite-dimensional closedness/projection nodes: those nodes assume generic complete or real/complex inner-product settings and do not state nearest-point attainment for a discretely valued ultrametric norm with no completeness of the ambient space.

`lem-sfb-ultrametric-orthogonal-extension` vs existing orthonormal-basis and Gram–Schmidt nodes: those nodes concern real/complex inner-product orthogonality and do not give the ultrametric residual-extension formula over a finite extension of `Q_ell`.

Neither new node restates the whole item or its continuity clause; both are proper finite-stage lemmas used by step 1.

## Review by NK

I read the current item node, the `sec-six-functors-basics` chapter record, the `sk-thm-sf-ctf-stability` unit record, and the complete main-20261015 proof paragraph cited by the item. The paragraph uses this result as the geometric norm-coefficient projection auxiliary and gives no external proof for the finite-dimensional induction. I also read the existing definition `def-weil-l-adic-coefficient-extension`, including its uniqueness and nonarchimedean restriction of the extended absolute value.

Step 1 uses exactly the statement of `lem-sfb-ultrametric-orthogonal-extension`: the current family is finite, the next generator is outside its span, and the node supplies a residual whose enlarged family satisfies the displayed max-norm formula. Processing a finite or countable spanning sequence gives an independent spanning family, hence a finite or `N`-indexed algebraic basis. I checked the prescribed `b_0=v_0` case and the case where all later generators are discarded.

Step 2 is elementary from the finite-stage orthogonality formula: finite support in the countable case lies in one stage, and empty support gives zero with maximum zero. Step 3 uses the coefficient-extension definition for `|ell|_E=|ell|_ell`, so `q=|ell|_E^{-1}>1`. Powers of `q` place every nonzero norm in one interval; multiplying by the corresponding power of `ell` preserves the basis and orthogonality, leaves the prescribed first vector fixed, and gives constants `c=min(||b_0||,1)` and `C=max(||b_0||,q)`. Step 4 derives coefficient and projection bounds directly from the exact norm formula, including arbitrary coordinate subsets, basis-to-subset maps, and the inverse when the subset is bijective with the full index set. No step uses a hidden infinite sum.

For the new nodes I checked every introduced object and hypothesis. The best-approximation node is strictly finite-dimensional and does not assert ambient completeness. The extension node assumes the exact max-norm orthogonality formula and only adds a vector outside the finite span, so it is narrower than the item. Both sources point to the same blueprint paragraph and mark the missing exact reference as WANTED. All citations in `citations.json` are literal substrings of the cited statements, and `proof_deps` is the union of the item’s step uses. Small cases checked: one-dimensional `V`, `V=E^d`, a redundant spanning sequence, a finite-dimensional space, the empty coefficient support, and a countably infinite sequence. No statement dispute was found.
