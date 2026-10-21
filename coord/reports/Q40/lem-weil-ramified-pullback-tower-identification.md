# Q40 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors/lem-weil-ramified-pullback-tower-identification.json`: existing statement, now split into nine proof steps; statement and inherited metadata unchanged. Mathlib verdict: no exact or one-line match for the whole tower assertion.
- `citations.json`: eighteen verbatim statement excerpts, one per step/node citation.
- `searches.jsonl`: seven searches from the retained delivery performed with the mandated msearch.py; the item's six inherited searches are retained in its JSON. Search results were read, with the most relevant declarations read in the local Mathlib source.
- `report.md`: this report. `write_split.py` is sandbox-only preparation code and is not a delivered node.

There are **0 new nodes and 0 new Mathlib leaves**. No Lean was written; no compiler, Lake, build, local preflight or forbidden git command was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and ramified pullback/tower terminology, and read the integral scalar-change search context. No declaration states this full item. General ring quotient or module pullback declarations do not constitute project attachments.

## WANTED

None needed for this split. The existing DVR theorem already records that Serre, Local Fields, Chapter II, section 2, Proposition 3 and corollaries, is wanted upstream. This delivery uses that existing theorem's stated uniformizer factorization, rather than claiming to have read the missing book or to have proved it here.

## What needed repair or clarification

The item arrived with no proof. Its source lists Stacks 093M, which gives completed constant coefficient quotients but does not state this ramified pullback-tower theorem. I therefore marked the proof as agent-written and supplied the coefficient, balancing and transition calculations explicitly. The imported statement is correct and was retained verbatim. In its local formula, the symbol p on the L side means p tensor 1 in Q=P tensor S_Y; Step 6 writes that insertion explicitly.

I read the assigned chapter and unit records and the current main-20261015 blueprint ancestor `def-weil-global-geometric-frobenius` (transport along g_Y). This is an auxiliary coefficient identification inherited through the parent scalar-comparison split, not the key statement of the f-shriek unit. No chapter, unit route or realization fields were changed. The four generic off-unit results used as tools are declared in split_report.tool_uses, with their roles and the reason they are needed.

## Unfinished work

None at stage 1. The existing theorem dependencies remain their own DAG items; this delivery does not claim to close their Lean proofs.

## Not duplicates

No new nodes were created. DAG and whole-blueprint searches for ramification, completed coefficients, completion-flat, and ramified pullback found existing local-field, completion and tensor tools. I reused them. The blueprint node `lem-coef-finite-free-extension` additionally assumes separated finite-type schemes over the global field and concerns derived direct/exceptional images and duality. It does not state this arbitrary-morphism, arbitrary-complex strict pullback-tower identification and was not substituted for it. `lem-weil-finite-free-completed-scalar-comparison` gives a derived-complete scalar-extension comparison, which is stronger than needed in one direction but does not give the specified finite pullback-tower maps. No duplicate or clause node was introduced for either one.

## Review by Q40

I read coord/delivery-errors.md B through E (including the retained duplicate sections), with the item and every cited node's statement open. I read the actual Stacks sites-modules.tex statements and arguments at 093M (lemma-completion-flat) and 03EL (lemma-tensor-product-pullback), the adjoining balanced tensor discussion of 03EK, and Bhatt–Scholze PDF pages 58–59, Lemma 6.8.2(1). The last source identifies the completed coefficient sheaf as the inverse limit of constant quotients; it does not prove the tower theorem by itself. No SGA source is used. There are no new-node sources to review.

Step 1 uses `lem-weil-l-adic-extension-absolute-value` exactly for uniqueness of the extending absolute value, and `lem-weil-l-adic-extension-integers-dvr` for the PID property, unit characterization and uniformizer factorization. These statements apply to both finite extensions of Q_l. Restriction from L to E gives an extending absolute value on E. This proves positivity of e and the equality of ideals; no global scheme hypothesis is taken from a more restrictive coefficient-comparison node.

Step 2 uses `def-weil-integral-scalar-extension` for the specific same-index iota maps and rho components, `def-weil-completed-integral-coefficients` for the actual inverse limits and projections, and `def-weil-proetale-inverse-image` for the constant coefficient structure maps. Its factorization at em is a quotient calculation: t^m maps to zero modulo v^(em). In this repair, naturality is checked first between finite constant sheaves by their adjoint presheaf maps; the two completed-sheaf maps are then compared after every finite projection. Thus the ring map R to S is the one specified by the existing scalar-extension construction.

Step 3 uses only the explicitly quoted canonical degree-zero quotient clause of `lem-weil-pbc-constant-completion-equivalence`: the projection induces Ahat/I^n Ahat = underline(A/I^n). The rings here are Noetherian because they are PIDs, and the pro-etale sites are taken in the stipulated small skeleton/sheaf universe. This clause needs neither derived completeness of P nor noetherianity of the schemes. The existing node is not being cited for a property hidden in its proof. The equality t^m S=v^(em) S follows by multiplying by the constant unit u^m and its inverse.

Step 4 uses the sheafified balanced tensor of `def-pur-sheaf-tensor-product` and the bilinearity, restriction compatibility and extensionality actually stated by `def-weil-pbc-ringed-tensor-section-calculus`. I wrote both quotient-tensor maps and checked both composites and the relation for t^m. It is an elementary step, not a new generic quotient lemma. Local lifting of quotient sections is handled by sheafification, so no global lift is assumed.

Step 5 uses `lem-weil-pbc-algebraic-inverse-image-tensor-comparison` precisely for tensor preservation and its pure-pairing formula, with the geometric inverse image of `def-weil-proetale-inverse-image`. Its hypotheses hold for g's small pro-etale topoi and the actual inverse-image ring/module objects. The latter definition also specifies the coefficient structure map used in finite module pullback. The reassociation maps and their inverses are written out and their normalization is tested by the pure pairing of `def-weil-pbc-ringed-tensor-section-calculus`. In self-review I removed an unnecessary citation of the finite constant-ring isomorphism: cancellation of a scalar tensor only needs the structure map, not its invertibility. In particular I never identify inverse image of a completed coefficient ring with completion on X.

Step 6 reuses the same normalized inverse-image tensor theorem for P tensor S_Y, and the balanced tensor and pure-section nodes for the explicit reassociations. Both sides are reduced to the same complex N tensor_H B_(L,X,em). This is the proof of the pullback isomorphism, not an appeal to a new node restating that clause. The expression with p tensor 1 in Q yields the item's exact local formula. The differential and every chain map act only on p, so the isomorphism holds for arbitrary, possibly unbounded and non-flat complexes. No K-flat, finite-Tor, constructible or derived-complete hypothesis was imported.

Step 7 uses `def-pur-integral-derived-operations` only for the specified finite pullback and quotient transitions after restriction of scalars; it uses the pure-section node for equality of sheaf maps. It checks both coefficient factors against q_(e(m+1),em) j_(m+1)=j_m q_(m+1,m), and checks the completed scalar against the limit projection identity. This proves transition compatibility by calculation. Naturality replaces p by f(p) in exactly the same formula.

Step 8 uses the scalar-extension definition's specified iota_m and the integral-operations definition's specified transitions. Both identities q_(em,m) j_m=iota_m and q_(em,m) pi_(em)=pi_m are reductions of the same element. Substitution gives precisely T_(m,em) followed after dtilde_m, in the requested order. Only the strict e-subsequence is asserted, so no derived-limit/cofinality comparison is hidden in this step. Step 9 is an elementary inspection of the constructed maps: none uses u except to establish equality of ideals.

I tested E=L and e=1, m=1, zero complexes, empty schemes, arbitrary non-flat terms, and a genuinely ramified point case. For E=Q_l and L=Q_l(v) with v^e=l (e>1), the coefficient map is O_L/l^m=O_L/v^(em). For g=id and P=R in degree zero, the same-index map is the quotient O_L/v^(em) to O_L/v^m. It kills v^m, which is nonzero at level em. This verifies the reason the statement must not assert injectivity. Replacing t or v by a unit multiple leaves the quotient ideals and all formulas unchanged. For the zero and empty cases the inverse maps remain valid in the zero module/ring sheaf.

B: no new statement-only or definition nodes were needed; citations quote actual statements, not tags as definitions. C: each non-elementary input has its own cited node, and all eighteen quotes are verbatim substrings. Dependency inspection found no path from the cited theorem dependencies back to this item. D: the nine steps carry the argument, with no relabelled clause or circular helper. E: I checked all hypotheses above, the sites and scalar actions on both sides, and the explicit transition formula. No statement dispute or source error was found. All non-elementary steps are below 2000 characters; none hides a comparison in a long paragraph.

## Repair of return L

The return reported a side-project completion that had not been promoted into the live queue DAG. The retained dry-run receipt named head `88ffe199c8b`; I kept its split, citations, report and search log. Before editing, the required initial dry run rebuilt that retained delivery on the current server DAG and passed at `330e48d2a60` (not pushed). I compared the sandbox node field by field with the current shared live node: the live item is `unsplit`, with no proof or split report; its statement, statement dependencies, source, creation metadata and blueprint attribution agree with the retained delivery. I reconstructed the item from that current live record and overlaid only the six fields owned by the split. The final delivery tool will again build on the current server base.

I reread every current proof citation, rather than relying on the earlier approval: `lem-weil-l-adic-extension-absolute-value`, `lem-weil-l-adic-extension-integers-dvr`, `def-weil-integral-scalar-extension`, `def-weil-completed-integral-coefficients`, `def-weil-proetale-inverse-image`, `lem-weil-pbc-constant-completion-equivalence`, `def-pur-sheaf-tensor-product`, `def-weil-pbc-ringed-tensor-section-calculus`, `lem-weil-pbc-algebraic-inverse-image-tensor-comparison`, and `def-pur-integral-derived-operations`. I also reread all statement-only dependencies, the chapter/unit records and the blueprint ancestor. All eighteen retained quoted clauses still occur verbatim in these current statements, and no cited id is missing or merged. In particular the current completion statement explicitly supplies the degree-zero quotient clause, and the current tensor comparison supplies its normalization on the actual pure pairing. Their broader derived assertions are not needed here.

Rereading the inverse-image definition prompted a concrete clarification in Step 2: a map from a completed coefficient sheaf is compared after each finite projection, not by asserting that global constant sections generate that completion. The revised step writes the naturality square for the finite constant-ring maps, proves it using their adjoint presheaf construction, and precomposes with the finite projection before applying the inverse-limit universal property. This uses exactly the same three cited statements, so the retained citation quotes remain applicable. The argument is elementary and introduces no hidden theorem or new node. Steps 1 and 3–9 and all recorded searches are retained.

I rechecked B–E with the revised step: its finite-index maps have the same domain and codomain, and projection equality proves the required scalar-action square without exchanging inverse image with an infinite limit. The remaining steps use only the hypotheses checked above. The examples e=1 and a genuinely ramified point still give the stated coefficient formulas and the noninjective same-index quotient. Every non-elementary step remains shorter than 2000 characters. No statement correction, extra hypothesis, new node, Lean change, or compiler invocation was needed.
