# Q02 stage-1 report: lem-sf-etale-proetale-exceptional-transport

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-etale-proetale-exceptional-transport.json` — split statement node, no Mathlib match.
- `citations.json` — 18 verbatim step/node statement quotes, expanded to include the actual formulas and hypotheses.
- `searches.jsonl` — the retained required Mathlib searches and a corrected grep against the Mathlib root, recorded by `msearch.py`.

## Attachments

None. No sorry-free declaration in the read-only source states this complete transport statement.

## WANTED

None.

## Not duplicates

- `lem-sf-etale-proetale-exceptional-transport` vs `thm-sf-ambient-adjoint-class`: the existing theorem gives the bounded-below relative adjunction for an étale-origin input, while this node additionally transports constructible finite-Tor objects, the compact-support comparison, and the explicit pro-étale counit formula.
- `lem-sf-etale-proetale-exceptional-transport` vs `lem-sf-class-compact-support-comparison`: that node only compares the two compact-support composites on an étale-origin witness; it does not construct the exceptional object or its Hom bijection.
- `lem-sf-etale-proetale-exceptional-transport` vs `lem-pur-exceptional-mate-site-comparison`: that node compares exceptional base-change mates in a Cartesian square, with no assertion of the present ordinary-to-pro-étale adjunction transport.
- `lem-sf-etale-proetale-exceptional-transport` vs `sk-thm-pe-constructible-comparison`: the existing comparison theorem supplies only the constructible site equivalence; it does not mention compact supports, the ordinary exceptional right adjoint, or the counit.

## What was wrong or repaired

The shared node was an unsplit statement-only child of Step 8. I retained its hypotheses and conclusion and supplied the missing proof. I checked that the field is allowed to be an arbitrary characteristic-$p$ field: the proof uses the generic Noetherian/quasi-compact constructible comparison theorem, rather than a finite-field-only comparison node. No hypotheses were added or dropped. The prior imported Mathlib searches were retained after reading their results, and the four required searches were rerun for Q02; all returned no declaration stating this package. No new DAG nodes were needed.

## Prior attempt review (superseded below)

I read the item statement and its source place, the parent unit proof at Step 8, and the statements of every cited node: `sk-thm-pe-constructible-comparison`, `lem-sf-comparison-pullback-exact`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `det-pe-classical-sheaves-modules`, `lem-sf-class-compact-support-comparison`, `def-amb-etale-compact-support`, `def-sfb-finite-derived-lower-shriek-compactification`, `thm-weil-pbc-site-comparison`, `thm-amb-etale-exceptional-adjoint`, and `def-weil-pbc-adjunction-mate`. Their statements say exactly the facts used: constructible complexes are equivalent across the sites for a discrete Noetherian coefficient ring; comparison pullback is exact and fully faithful on sheaves; derived tensor commutes with pullback; the compact-support composites for the same compactification compare canonically; the ordinary compact-support functor has the stated right adjoint; bounded-below comparison is fully faithful; and adjunction mates are characterized by counit transposition.

Step 1 checks that the finite coefficient ring is Noetherian and that finite-type schemes are quasi-compact and quasi-separated, then obtains an étale-origin witness from the generic constructible equivalence. For an arbitrary étale module sheaf in degree zero, the derived tensor pullback formula and exact comparison identify its pulled-back cohomology with the pro-étale tensor used in the given Tor-amplitude hypothesis; full faithfulness reflects vanishing, so the witness has the same Tor interval. Step 2 applies the assumed preservation of bounded constructible finite-Tor complexes by $f^\times$, then transports constructibility and the Tor interval along exact comparison pullback. Full faithfulness supplies the unique maps between alternative witnesses, establishing naturality and witness independence.

Step 3 applies the existing compact-support comparison to the identity witness for every bounded-below étale complex $M$ and inverts its orientation to obtain $\nu_Y^*F_{\mathrm{et}}\simeq F_{\mathrm{proet}}\nu_X^*$. Step 4 writes the Hom chain explicitly: pro-étale compact-support comparison, bounded-below site full faithfulness, the ordinary $F_{\mathrm{et}}\dashv f^\times$ adjunction, and full faithfulness on $X$. This gives exactly the displayed Hom bijection. Step 5 checks naturality in both variables and independence of the chosen origin witness by the unique lifted witness morphism. Step 6 reads the ordinary Hom bijection as postcomposition with its counit and transports that counit through the same comparison maps; the mate statement and triangle identities give precisely $h\mapsto t_K\circ F_{\mathrm{proet}}(h)$.

I tested the edge cases $f=\mathrm{id}$, $X=\varnothing$, $Y=\varnothing$, and $K=0$: the comparison and counit formulas reduce respectively to identity, zero, zero, and the unique zero Hom map. The item has no long hidden lemma step over 2000 characters, no SGA citation, no new node, and its proof dependencies are exactly the union of the step uses.


## Review by Q02

This is the resumed review, superseding the earlier proof-specific account above. I retained the earlier item, report, searches and citations, compared the statement with the current shared unsplit node (unchanged), and ran the required dry run first. It exited with a short-quote error for the pro-etale compact-support definition; nothing was pushed. I replaced the citation entries by the complete cited statements so the formulas and hypotheses, rather than a vague introductory sentence, can be checked directly.

I read the chapter and unit records, the main-20261015 unit proof, and the current parent DAG proof Step 8. The blueprint text has no numbered Step 8: it has the final restriction paragraph. The imported source locator refers to the current DAG parent's transport step. I therefore corrected proof_origin to agent and explained that locator in split_report. This is the explicit site-transport argument requested by that parent, with no change to the unit's preservation route or to the item's hypotheses and conclusion.

Step 1 uses lem-weil-pbc-finite-type-over-noetherian to check Noetherian schemes, sk-thm-pe-constructible-comparison for the bounded constructible equivalence, and lem-exc-comparison-tor-interval to reflect the Tor interval. I read all three statements: the first applies over Spec k since a field is Noetherian; the second requires discrete Noetherian A and qcqs schemes, satisfied because A is finite and the schemes are separated of finite type; the third allows any finite commutative ring and explicitly tests every module sheaf. It has no finite-field hypothesis. Step 2 uses the same constructible equivalence and the forward implication of the Tor-interval theorem, after applying the preservation hypothesis on f^times. This corrects the previous unsupported ascent argument: exactness and a tensor comparison evaluated only on classical test modules do not by themselves prove the claimed bound against arbitrary pro-etale modules.

Step 3 replaces lem-sf-class-compact-support-comparison entirely. Reading its statement revealed that it assumes A=O_E/varpi_E^n, which cannot be inferred for an arbitrary finite ell-primary ring (for instance F_ell[x,y]/(x,y)^2 has nonprincipal maximal ideal). Instead I read sk-thm-pe-direct-image-comparison, which allows every discrete commutative ring and every qcqs scheme morphism, and lem-cbc-proetale-extension-zero-comparison, which allows every finite commutative ring and open immersion. Their respective formulas compose to the required comparison for the same fixed compactification. Proper p_f is qcqs; the input j_!M is bounded below by the exactness statements lem-weil-pbc-extension-by-zero-exact and lem-sfb-finite-extension-by-zero-exact. The exact comparison pullback is lem-sf-comparison-pullback-exact. I read both compact-support definitions to confirm they are exactly these composites. I also read Stacks proetale.tex Tag 09A6, label lemma-morphism-comparison, Tag 09AF, label lemma-jshriek-comparison, and Tag 099V, label lemma-relative-comparison. These give the source comparisons; the module-coefficient statements cited in the DAG already carry their extension to module sheaves. No restricted-coefficient compact-support lemma is needed.

Step 4 uses bounded-below full faithfulness from thm-weil-pbc-site-comparison, the D+ direct-image comparison just read, and thm-amb-etale-exceptional-adjoint. I opened these statements and checked finite A, Noetherian schemes, the open/proper finite-type compactification, and bounded-below inputs at both full-faithfulness applications. The input E and output RE are bounded by Steps 1 and 2. The entire Hom chain is written explicitly and uses the ordinary unbounded adjunction only between objects already in D+.

Step 5 uses only the fully faithful comparison statement and elementary uniqueness: the lift of alpha'^{-1} v alpha defines the morphism, and faithfulness proves the identity and composition laws. Step 6 writes t_K=alpha Q(epsilon_E) beta_RE^{-1} and substitutes the unique lift h=P(u); the naturality equation for beta^{-1} gives the exact requested counit formula. Counit naturality gives t_K' G(PR(u))=v t_K. This is a few-line calculation from the cited adjunction and full faithfulness. I removed the prior mate-definition citation, since a mate definition alone does not prove the formula and invoking a second ambient pro-etale adjunction here would be unjustified.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the revised files. No new nodes are created, so no duplicate/elementary/restated-clause leaf is introduced and no new-node search is fabricated. The existing no-duplicate comparisons above remain relevant. The second Mathlib phrasing is the retained LeanSearch question; I read the logged hits, which give generic sheaf adjunctions, not the present transport statement. The prior grep passed Mathlib/ as a subdirectory, producing no hits in a doubled path; I reran that query with no subdirectory, read the actual topological-support hits, and recorded their actual result. Imported search records remain retained. Source searches in WeilConjectures found the pro-etale UpperShriek transport declarations, but they do not state the constructible finite-Tor preservation clauses of this entire item, so no attachment is claimed.

Small cases: f=id reduces beta and the counit to the identity comparisons. For X empty, both source Hom sets are singletons; for Y empty any f has X empty. K=0 gives the zero adjoint object, and A=0 gives zero module categories. A=F_ell[x,y]/(x,y)^2 is allowed in every cited comparison, so the repaired proof handles the coefficient case missed before; arbitrary characteristic-p fields need no finite cohomological-dimension bound. Witness changes were checked by lifting their inverses. All six steps are shorter than 2000 characters and have no hidden comparison lemma. No SGA source is used. The proof dependency list is precisely the union of step uses; off-unit statements are declared as generic tools.

## Remaining work

No mathematical gap identified in this split. Server dry run and push follow this signed review.
