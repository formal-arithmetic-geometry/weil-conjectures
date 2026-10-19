# Q127 report: det-sp-p1-trace

Files written:

- `dag/nodes/sec-six-functors-basics/det-sp-p1-trace.json` — existing statement node, repaired into 11 proof steps; no new nodes and no Mathlib leaves.
- `citations.json` — 46 verbatim step-to-node citations.
- `searches.jsonl` — retained prior searches and four additional `msearch.py` searches; LeanSearch was recorded unavailable because of the service rate limit, while Loogle, LeanFinder and grep ran.

Attachments: none. The source checkout contains no declaration tagged `(blueprint: det-sp-p1-trace)` that proves this item, and the node remains a stage-1 natural-language item.

WANTED: none.

The retained split was returned because former steps 1 (2058 characters), 4 (2038 characters), and 7 (3534 characters) were long non-elementary arguments. I kept the statement and route unchanged. I divided step 1 into projective qcqs/Noetherian hypotheses and the explicit diagonal Cartier and closed-direct-image calculation. I divided step 4 into the exact bounded-below comparison transport and its mate-pasting base-change compatibility. I divided step 7 into (i) transport of the auxiliary ordinary-etale diagonal integral, (ii) normalization of the canonical composite-adjunction unit using the derived pushforward-composition comparison, and (iii) comparison of the two Chern-class composites to conclude the integral for the precise Cartier class `c_Delta`.

## Review by Q127

I read the current item statement, its blueprint statement and proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/det-sp-p1-trace.proof.md`, the unit record `sk-prop-geo-p1-adjunction`, and every cited DAG statement. The projective-space pullback and properness nodes supply the identifications and proper qcqs hypotheses in steps 1–2; the finite-type-over-Noetherian and closed-immersion nodes supply the Noetherian and proper diagonal claims. The standard-chart and divisor-definition statements supply the equations `x-y` and `xy-1`, their non-zero-divisor check, and the line-bundle interpretation; the pro-etale open/closed statement supplies exactness and the derived identification for the diagonal pushforward.

For steps 3–4 I checked the ordinary finite projective-line decomposition, its normalized twisted version and trace, the proper projection formula, finite-twist pullback, torsion proper base change, mate pasting, standard charts, and supported Kummer statement. Their hypotheses are `A = Z/ell^n`, `N = ell^n`, `S` Noetherian with `ell` invertible, and the base-changed projective lines; these are verified explicitly before use. The comparison-pullback and derived-pullback nodes justify termwise exact transport and bounded-below preservation. The direct-image comparison node applies because all maps are qcqs and all inputs are sheaves, shifts, or the exact closed pushforward; the mate-pasting citation says precisely that the exchange squares agree after comparison.

For steps 5–8 I checked the twisted projection formula definition of the trace, the construction of `Spec Z[1/ell]` as the universal Noetherian base, and the standard-chart computation for a geometric rational point, including both coordinate points. The equality `O(x) ≅ O(1)` gives equality of Kummer Chern classes and hence trace one. For steps 9–11 I read the ordinary diagonal-integrals statement, supported Kummer statement, bounded-below comparison, derived pushforward-composition normalization, composite-adjunction unit formula, mate-pasting statement, and `sk-lem-geo-cartier`. Step 9 transports only the auxiliary etale class. Step 10 proves that the canonical `alpha_a` is the composite-adjunction unit under the normalized composition isomorphism. Step 11 uses the two cited Chern-class identities and compares their composites with the unit, avoiding any unsupported equality of supported morphisms; composing with the already established auxiliary integral gives the required identity for exactly `c_Delta`.

All 11 proof steps are below 2000 characters, every non-elementary dependency is named in `uses`, `proof_deps` is their union, and each citation quote is copied verbatim from the cited node statement. No SGA 4 source is used, no statement or hypothesis was weakened, and no new node was introduced.

On resumption after the provider interruption, the required dry run reported that the saved node still had `status: unsplit`. I set it to `split`. I also corrected step-number references left stale by the previous subdivision and moved the closed-etale-direct-image citation from step 6 to step 5, where that fact is used. The current repository statement matches the saved statement verbatim; no source, statement, or route changed.

Nothing remains unfinished.
