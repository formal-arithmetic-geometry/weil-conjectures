# Stage-1 report: lem-coef-dualizing-support-evaluation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dualizing-support-evaluation.json`: statement, split using 16 existing proof dependencies; unchanged statement and statement dependencies. The item is not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every node cited in every numbered proof step.
- `searches.jsonl`: actual searches logged by the required search command.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No unit or chapter record changed. No Lean written or compiled; the repository and launcher were read only.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and the notions dualizing/support/evaluation and semilinear quotient derived systems. Hits about Poincare pairing, scalar changes, and ordinary cohomology evaluation do not state the simultaneous varying-coefficient compact-support assertion. The existing helper declarations under `Sheaf/` are statements already associated with their DAG nodes, not attachments of this item.

## WANTED

None. The current blueprint extraction, Zheng, and all relevant Stacks source files are available locally. Some newly imported nodes retain old blueprint source paths; I read the current main-20261015 version at `sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md` alongside the archived master file.

## Findings and changes

The input was statement-only and unsplit. No statement dispute was found. The proof now constructs evaluation before taking any limit, identifies the transition as an actual scalar-adjunction transpose, and derives its alternative restriction-comparison expression. It then derives point sections separately. The final conditional clause is checked on the finite constructible etale-origin realization and does not impose constructibility on the arbitrary strict input.

A tempting false shortcut would be to claim varying-ring evaluation preserves K-injectives, or that constant coefficient restriction preserves them. Neither is used. Another shortcut would be to replace derived sections at the pro-etale point by ordinary sections on arbitrary inputs; this is not used either. The output is in the derived category of strict constant-R towers, not just a diagram in D(R), and no inverse limit is inserted.

The whole proof can use existing nodes. I searched the whole DAG for sequence evaluation, derived sections, scalar mates, support restriction, coefficient comparisons and their Stacks tags, and used `tools/blueprint_refs.py search` for semilinear, compact support, and evaluated compact support. The last returned no exact blueprint node. Related blueprint nodes include finite-dualizing and compact-support-coefficient-change, which cover only finite constructible clauses, not the full arbitrary-input tower statement. The item's existing blueprint ancestry and place were retained; `same_as` remains empty. No new nodes were proposed, so none can be an elementary-node, clause-restatement, or duplicate error.

## Mathlib searches

The five fresh searches are recorded verbatim in the item and in `searches.jsonl`. All services answered. Loogle (`"SheafOfModules", "derived"`) and the grep for compact-support/semilinear quotient-derived transitions had zero hits. LeanSearch returned ordinary module-sheaf pushforward and sections declarations, with signatures defining the underived functor or its underlying sections. The first LeanFinder query returned adic-completion transition/evaluation lemmas and unrelated profinite algebra; the second returned structure-sheaf sections on Spec and tilde-module restriction identities. None concerns ordinary derived semilinear quotient systems or the specified compact-support mates. The second semantic phrasing was read before concluding no match. Original recorded searches were retained as source material and not claimed as fresh Q57 searches.

## Review by Q57

I read delivery-errors B--E in full, the worker/stage-1 rules, the three blueprint levels in SETUP, GOAL, the item and its chapter/unit, and the finite-dualizing/integral-dualizing blueprint proofs. The route remains the construction of the specified finite adjunction maps before taking limits in paragraph 2 of integral dualizing. There is no use of any SGA source.

For the human sources, I read Zheng Construction 4.1 (printed page 21) and Lemma 4.10 (printed page 23): they construct the quotient sequence ringed topos and give the unbounded derived direct-image evaluation isomorphism by evaluation-adjunction base change. The distinction between varying coefficients and constant coefficients is explicit there. I read Stacks 0941 (`sites-cohomology.tex`, `lemma-derived-limit-is-ok`), especially the exact left-adjoint argument for *constant*-coefficient evaluation; it is not asserted for varying-ring K-injectives. I also read 0D6E (`lemma-derived-pushforward-composition`), 07A6 (`lemma-adjoint`), 03DI and 03DJ (`sites-modules.tex`, `lemma-extension-by-zero` and `lemma-extension-by-zero-exact`), 0GL1 (`sites-cohomology.tex`, `lemma-j-shriek-and-tensor`), and 0B56 (`equation-projection-formula-map`). These sources supply the constructions; the full coherence normalization is an agent argument supported by the existing DAG statements, so proof_origin is agent, not an attribution of the whole statement to a Stacks tag.

I opened and read the statement of every proof dependency, rather than borrowing their proofs. The per-step check was:

1. `def-coef-ringed-sequence-site` defines exactly the quotient-semilinear system/evaluation realization. `lem-coef-semilinear-derived-sections` explicitly states exact evaluation, the proper direct-image comparison, and exact open localization on ordinary unbounded system categories. I applied these to p and j with the actual constant A_n inverse-image identifications. Normalization is unnecessary and no injective-evaluation assumption appears.
2. The same semilinear theorem states its direct-image transition formula G_n(t)b. `lem-fix-open-scalar-tensor-normalization` supplies precisely the open scalar isomorphism beta; substitution gives F_n(alpha)c with its correct order. The proper coefficient map is not assumed invertible for arbitrary Q.
3. `lem-pur-sheaf-ring-derived-coefficient-adjunction` states the unrestricted scalar adjunction with the actual representative unit. The standard inverse Hom correspondence sends v to Res(v) eta, giving the d in the question. The relevant quotient ring maps need not be flat.
4. `lem-sf-compact-support-restriction-of-scalars` states the natural proper/open restriction comparison rho for the fixed compactification. `def-coef-compact-support-tensor-comparison` actually defines the comparison by its scalar-unit equation; it is not cited as an invertibility theorem. `lem-weil-pbc-mate-pasting` identifies its proper/open mate word with step 2. Naturality of rho then proves d = rho F(sigma) by the displayed calculation, for arbitrary alpha rather than an isomorphism.
5. `lem-coef-semilinear-derived-sections` applies also to global sections to the punctual topos with ring tower A_n. Its statement covers morphisms of topoi, not just scheme maps, and its ring inverse images are (A_n)_s here. It gives evaluation and actual transitions after this second derivation. `def-pc-sheaf-restrict-scalars` says the underlying abelian sheaf is unchanged; exactness and commutation with evaluation are justified explicitly from kernels/cokernels, not taken as an unstated theorem. Theta is the composite with RΓ(psi), in D(R).
6. Identity and composition follow by conjugating the actual strict tower equations by the natural isomorphisms of the semilinear theorem. This is a short elementary assembly, not a claim that level evaluations are faithful on arbitrary derived morphisms. It also explains dependence on Q and the fixed compactification.
7. `lem-coef-dualizing-construction` explicitly gives bounded constructible finite-Tor etale omega, and `lem-weil-finite-duality-site-comparison` gives its pro-etale realization. `lem-fix-reduction-open-etale-origin` explicitly includes boundedness of j_!omega and its derived reduction on the etale site. These verify the bounded-below hypotheses needed next, including reduction boundedness despite nonflat quotient coefficients.
8. `lem-sfb-etale-proetale-scalar-mate` states equality for the actual B-linear proper coefficient mate, under qcqs and the two bounded-below conditions established in step 7. Proper p is qcqs. `lem-fix-open-scalar-tensor-normalization` and `lem-fix-site-open-exchange` specify open comparisons by their units; the latter's statement includes this normalization, not only an unrelated square. The scalar/pullback cube in `lem-sfb-etale-proetale-scalar-pullback-cube`, together with `lem-weil-pbc-mate-pasting`, identifies the open mate words. Pasting with the proper equality identifies c with the etale compact-support tensor comparison of `lem-fix-compact-support-coefficient-change`. `lem-coef-finite-dualizing` names exactly that comparison in its counit definition. This argument stays on finite constructible realizations and asserts no ambient pro-etale exceptional adjoint.
9. Substitution alpha=u in the established formula proves the conditional conclusion. `lem-coef-finite-dualizing` states that u is the counit-defined map and that its finite pro-etale realization is the transported map; no alternative choice of u is made.

I checked all 22 uses entries against the actual node statements and wrote exact quotations in citations.json. Generic off-unit tools are declared in split_report.tool_uses with their purpose; they support the specified construction rather than change the unit route. All nine steps are shorter than 2000 characters. The detailed source normalization in step 8 uses existing scalar-cube and mate-pasting theorems, rather than hiding a new comparison lemma.

Small cases checked: Q=0 and X empty give zero objects and zero maps; m=n makes alpha, beta, b and the scalar unit identity, hence d=1. For a triple r>=m>=n the already strict transition equations give the same equation after each natural comparison. For X=s with identity compactification, the formula is the ordinary scalar-unit transpose of sigma. Noncartesian Q and nonflat reductions (for example Z/4 -> Z/2) are allowed throughout the arbitrary-input proof; c is only a map. The finite-Tor hypothesis is established solely where the final dualizing site-normalization argument needs bounded reductions. No uniform bound in n, exact products, coefficient-flatness, or ordinary inverse limit is used.

Corrections made while checking: point sections are explicitly derived to the quotient-system category on the point and only then restricted to constant R; restriction exactness is explained from its underlying sheaves; the proper scalar-mate site-comparison hypothesis is verified using the open reduction witnesses before it is invoked. The statement was preserved in full.

## Not duplicates

No new nodes. Existing nodes were reused for each genuine theorem, and elementary scalar-transpose substitution/coherence arguments remained steps of the item.

## Unfinished work

No missing stage-1 argument is known. The cited existing nodes remain their own independent DAG obligations; this delivery does not assert their Lean proofs are finished. Required server dry run and direct push follow this report.
