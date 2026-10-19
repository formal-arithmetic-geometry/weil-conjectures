# Worker report: lem-pur-etale-orientation-locality

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-coprojection-rho-compatibility.json`: new statement-only auxiliary lemma; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-pur-etale-orientation-locality.json`: repaired item; no Mathlib leaf.
- `citations.json`: verbatim quotations for every cited node in every proof step.

## Attachments

None. I searched the project source checkouts for the exact item id, title, and displayed comparison; no sorry-free project declaration states the whole item.

## WANTED

None.

## What was wrong and what I repaired

The returned version had four faults. I replaced the flawed `lem-pur-etale-geometry-stability` addition with the existing `lem-weil-pbc-etale-scheme-base-change` Mathlib leaf and the existing `lem-sbc-smooth-relative-dimension-permanence` route lemma, and removed the duplicate geometry node from this delivery. I corrected the auxiliary co-projection lemma so that `e:U -> X` is explicitly separated and finite type, and it now cites the existing étale base-change node. I repaired all malformed TeX (`\\rho`, `\\theta`, and `\\to`) and removed the stray Unicode rho. Finally, I added the missing `lem-pur-diagonal-dnc-chart-normalization` citation: its rank-zero clause has `P_0 = id` and identity standard section and bundle comparisons, which identifies the relative-dimension-zero diagonal orientation with `eta_e`.

## Review by Q89

I reread the item statement and the complete Step 4(i)--(ii) source in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/sk-thm-regular.proof.md`. I also read the full statements of every node cited in the five proof steps, including the existing étale base-change and smooth relative-dimension permanence nodes, the finite étale dualizing normalization node, the diagonal DNC chart normalization node, and the new co-projection compatibility node. The item's statement dependencies now name the existing geometry lemmas and the diagonal chart normalization needed for the rank-zero orientation clause.

Step 1 uses clauses (1)--(3) of `lem-pur-finite-etale-dualizing-normalization` for the normalized rho, composition, base-change, and dualizing comparisons; `sk-lem-regular-smooth` for smoothness of `a_X` and `a_Z`; `lem-weil-pbc-etale-scheme-base-change` for v; and `lem-sbc-smooth-relative-dimension-permanence` for smoothness and relative dimensions after base change and composition. I checked that the d=0 sentence of `lem-pur-diagonal-dnc-chart-normalization` supplies the identity comparison, so the unit orientation is the specified `eta_e`, and that `def-weil-etale-morphism` supplies the étale hypotheses.

Step 2 takes the chosen exceptional composition comparison from `pur9-def-upper-shriek-composition`, its associativity and unit law from `sk-thm-sf-compatibility`, and normalized rho composition from the finite étale normalization node. I checked the direction of each inverse and the fibre-product identity `u ∘ i_U = i ∘ v`.

Step 3 uses the orientation factors assembled by `pur9-rg-def-phi` and `thm-pur-diagonal-dualizing-object`. It checks the coefficient-unit transpose from `def-pur-co-smoothness`, the unit projection mate from `lem-weil-pbc-ringed-projection-mate-exact`, and the unitor in `def-exchange-projection`, then applies `thm-pur-composition-coherence` to the actual smooth factorizations. The added diagonal-chart citation supplies the rank-zero normalization, while clause (3) of the finite étale normalization identifies the E and sigma factors.

Step 4 checks the Tate twist hypotheses using `lem-pur-coprojection`, `lem-pur-twist-sheaf-locally-free`, and `def-coefficient-twists-detailed`. The new auxiliary node has the separated finite-type étale hypothesis, defines the five-arrow comparison `B_{e,i,K}`, and states exactly the co-projection square with the canonical pullback identification. The finite étale normalization and `def-exchange-projection` identify the chosen maps used in that square.

Step 5 expands `pur9-rg-def-phi`; `sk-thm-sf-compatibility` and the finite étale normalization identify the exceptional pastings, and the auxiliary node identifies each co-projection after base change. The existing smooth and étale permanence nodes supply the componentwise geometry, while `sk-lem-regular-smooth` supplies the original dimensions. I wrote the componentwise pasting explicitly and retained the varying-dimension and no-Kummer clauses.

I verified that every `uses` entry occurs in `proof_deps`, every `citations.json` quote is a verbatim substring of its cited statement, all new statements were tested on identity, open-and-closed, empty, zero-codimension, Tate-shift, and varying-component cases, and no Lean, compiler, Lake/build, live project, or launcher file was modified.

## What could not be finished

Nothing remains for this stage-1 repair; the server checks and delivery are next.
