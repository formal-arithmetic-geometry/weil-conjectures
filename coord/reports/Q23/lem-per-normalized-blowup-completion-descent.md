# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-normalized-blowup-completion-descent.json`: split item, unchanged statement, five proof steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-normalization-completion-base-change.json`: one new unsplit statement node for Stacks Tag 0BG9; Mathlib searches found no match.
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `report.md`: this report.

## Attachments

None. I searched the slopmaster2 source by the item id, normalized-blowup/completion terminology, and likely normalization declarations; no sorry-free project declaration states the item.

## WANTED

None. The Stacks source is present at `literature/stacks-project/resolve.tex`.

## Source and split

I read the item against `literature/stacks-project/resolve.tex`, especially Tag 0BGA (`lemma-normalized-blowup-completion`) and Tag 0BG6(3) (`lemma-port-regularity-to-completion`). I also read Tag 0BG9 (`lemma-normalization-completion`) in full; that statement is recorded as the new node `lem-per-normalization-completion-base-change`. The item statement is unchanged and retains its Noetherian local-domain, normal-completion, proper-normalized-point-blowup, structure-morphism base-change, endpoint-regularity, and length-zero clauses.

Step 1 is the induction setup from 0BGA. The cited completion definition and local-completion statement provide the common residue field, and the fibre-product and affine-spectrum definitions identify the closed fibres. I explicitly handled the empty/length-zero tower.

Step 2 cites the existing completion-flatness and flat-base-change statements, the existing flat blowup comparison `thm-nagata-blowup-flat-base-change`, and the blowup/fibre-product notions. These statements say exactly that the ordinary blowup at the descended closed point base-changes to the ordinary blowup at the corresponding completed point.

Step 3 applies the new 0BG9 node. Its statement supplies finiteness of the descended normalization and identifies its completed base change with the normalization of the ordinary completed blowup. The existing blowup-complement statement says the ordinary blowup is an isomorphism off its centre. The existing normalization-normal-stalks statement applies to the normalization in the generic function field and supplies normality of the normalized stages, so the complement of the special fibre is normal; I did not use the stronger excellent-tower theorem, whose excellence hypotheses are absent here.

Step 4 cites the existing properness of ordinary blowups, finite morphisms, and composition of proper morphisms. Together these give properness of each descended normalized blowup and preserve the centre-over-the-closed-point condition.

Step 5 follows 0BG6(3) pointwise. Completion is faithfully flat; flatness is preserved by base change; localizing the resulting flat map gives a flat local map, which is faithfully flat by the cited local lemma. The cited faithful-flat regularity descent then applies to each local ring, proving regularity of the descended endpoint. I checked that the selected point above every descended point is supplied by surjectivity of faithful flatness.

I tested the edge cases conceptually: length zero gives the identity and the regularity implication is immediate; a one-step tower has exactly one centre, one ordinary blowup, and one normalization comparison; an empty centre list does not occur in a nonzero tower and produces no hidden extra step. I also checked every cited node's statement while producing `citations.json`; each quote is copied verbatim from that statement.

## Not duplicates

`lem-per-normalization-completion-base-change` vs `lem-per-normalized-blowup-completion-descent`: the new node is the general normalization-completion comparison for one locally finite-type scheme under a normal-complement hypothesis (Tag 0BG9), while the item descends an entire finite tower of point blowups and also concludes properness and endpoint regularity (Tags 0BGA and 0BG6(3)).

## Review by Q23

I read the item and new node from their Stacks sources, checked all item hypotheses against the induction, and verified that the new node introduces its own scheme, completion, fibre product, normalization, finiteness, and normality notions through the listed dependency nodes. I checked each proof step against the exact cited statements, with the nontrivial completion-normalization comparison isolated in the new node and all generic blowup and commutative-algebra facts cited as tools. I corrected the initial draft of Step 3 by replacing an inapplicable excellent-tower citation with `lem-weil-pbc-normalization-normal-stalks`, which applies directly to normalization in the generic function field and avoids adding an excellence hypothesis. The Mathlib searches for the item and new node were run through `msearch.py`; LeanSearch, LeanFinder, Loogle, and Mathlib grep returned only relative-normalization or adic-completion facts and no match for the geometric assertion. No Lean files were written and no compiler or Lake command was run, as required for stage 1.

The dry run identified one packaging issue: the new 0BG9 statement initially omitted inline dependency citations. I repaired it by defining the special fibre explicitly and citing the Noetherian, completion, finite-type, fibre-product, affine-spectrum, normality, normalization, and finite-integral notions in the statement itself.
