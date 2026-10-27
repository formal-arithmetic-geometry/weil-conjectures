# Q136: lem-sf-proper-triple-counit-transpose

## Files written

- dag/nodes/sec-six-functors/lem-sf-proper-triple-counit-transpose.json: statement, split, no exact Mathlib match; statement unchanged.
- citations.json: eight verbatim statement quotations, one for every cited node at every step.
- report.md: this report. searches.jsonl is the search command's own log.

New nodes: 0. Mathlib leaves: 0. No unit record changed: this is not the unit's key statement.

## Attachments

None. Searched WeilConjectures by the exact blueprint id and the notions counit, tensor and Kunneth. Read SixFunctors/Etale/Derived/Kunneth/Comparisons.lean and Relative.lean, especially Relative.lean:132-143. The relative theorem gives a Nonempty isomorphism with a sorry, not the asserted equality of the specified maps and their transposes. No project declaration found states every clause without sorry. The existing binary node has a stage-2 theorem in Sheaf; that is a reusable DAG statement, not a finished attachment for this ternary item.

## WANTED

None. No literature downloaded.

## Findings and changes

The item had a statement and inherited Mathlib searches but no proof. Reused lem-sf-proper-product-counit-transpose, already split and reviewed in this same unit, rather than introducing a binary-transpose duplicate or a node for each parenthesization. Four applications of its statement provide the two inner transposes and the two outer transposes. The proof then inserts the inner map before transposing, using pullback-tensor naturality; the displayed calculations produce the same three counits in their original order.

Read the chapter and sk-thm-sf-kunneth-relative unit records, the current main-20261015 lem-sf-kunneth-coherence statement/proof, and the existing binary node's entire statement and proof. The blueprint sketches the associativity assertion and its two-counit input but does not supply this ternary computation; proof_origin is therefore agent. The proof realizes its clause (ii) and final counit sentence without changing the unit route. The chapter's historical prohibited-source references are not used or cited in the split. No SGA source is used.

The statement was well typed and no source correction was needed. In particular the outer maps initially take t_*A tensor H and F tensor z_*D; the proof explicitly inserts a tensor 1 and 1 tensor b before replacing the inner counit composites. Simply calling both outer transposes the three-counit map would have skipped this necessary calculation.

## Search evidence and duplicates

Ran the required leanfinder, loogle, grep and leansearch via msearch.py, with a second leanfinder phrasing. All five calls succeeded; exact query texts and returned names are retained in the item and searches.jsonl. Read Mathlib/CategoryTheory/Monoidal/Functor.lean:943-978,1033-1039 and LocallyCartesianClosed/ExponentiableMorphism.lean:40-49. The former supplies general monoidal right-adjoint structure and binary counit equations, while the latter concerns Over categories. Neither identifies the specified geometric exchange/PF composites with those counit maps for three different morphisms; there is no one-line specialization of the full item. The LeanSearch adjunction-triple hits concern successive adjunctions, not three product inputs.

Searched the whole DAG for counit/transpose/product comparisons and searched the blueprint with blueprint_refs.py for two-counit, triple and transpose. The existing binary node is strictly a two-input fact and is cited. The ancestor is lem-sf-kunneth-coherence, as already recorded. The blueprint coherence nodes state equality of the product maps, rather than this explicit three-counit transpose; same_as remains empty. There are no new-node pairs requiring a Not duplicates entry.

## Review by Q136

I read coord/delivery-errors.md B through E, including the duplicated historical block, against the actual node statements and sources. There are no new nodes, so no statement-only node, undefined-object, TeX, new-node source-tag or duplicate issue arises. Every new proof formula uses single TeX backslashes. I retained the item's original statement, source and metadata. Its existing definitions already introduce the coefficient data, bounded constructible finite-Tor categories and specified transformations.

Step 1 uses lem-weil-pbc-proper-fp-permanence precisely for its composition and arbitrary-base-change clauses (a),(b). I read Stacks morphisms.tex, lemma-composition-proper (01W3) and lemma-base-change-proper (01W4): products are proper by applying these to the two projections and composing. This verifies the extra pairs (t,h) and (f,z) in addition to the given (f,g),(g,h). The six-functor datum explicitly supplies its operations on finite-Tor categories and its adjunction (A1); the proof uses that supplied domain and does not derive closure from an unstated general theorem. I read def-sf-datum in full and def-exchange-projection and def-sf-pf for the coefficient conventions and the actual map formula. The transpose is the ordinary counit evaluation, so its source and target are checked directly.

Step 2 cites the statement, not the proof, of lem-sf-proper-product-counit-transpose. I compared its lambda formula, Psi, proper identification and adjunction-compatible composition comparison term for term with the item: they coincide. Its final displayed formula supplies exactly each of the four transposes after replacing the two arrows and two inputs. All properness and finite-Tor hypotheses were checked in Step 1. No proper base-change isomorphism or PF coherence theorem is silently added here: the binary statement already identifies the specified composite.

Steps 3 and 4 use the same binary formula for a and b and lem-pur-derived-pullback-tensor-iso for naturality, composition, associativity and signed tensor comparisons. I read that node's full statement and Stacks sites-cohomology.tex, lemma-pullback-tensor-product (07A4), including its K-flat construction. The node explicitly covers the higher coefficient conventions and all the comparison compatibilities used; the Stacks finite-level assertion is not substituted directly for completed tensor. The middle equalities in both calculations are only functoriality of pullback and bifunctoriality of tensor. Each pulled-back inner counit composite is replaced by a cited binary transpose; no hidden ternary lemma is assumed. The final pullback identifications are justified by the named projection equalities and the cited composition compatibility. The associativity compatibility identifies the two bracketings. No permutation is performed, so there is no residual Koszul sign to omit.

I checked the identity case f=g=h=id, where this gives tensor associativity with identity counits; the zero input and empty-fibre cases, where the counit composites remain well typed and vanish; and shifted inputs, where no extra swap is introduced. The calculation works on the integral category with completed operations and on the two field stages with their supplied common-stage comparisons; it does not use an unavailable rational-to-finite reduction or infer integral equality from all reductions. The ordinary counits used have their proper targets K,L,M, and the final source is v^*(F tensor G tensor H), not a tensor with an unpulled inner pushforward.

C1/C4: all non-elementary ingredients are cited as nodes; all eight citations were checked to be verbatim substrings of the cited statements. There is no dependence on the parent lem-sf-kunneth-coherence (which depends on this item), so the proof introduces no circularity. No relabelled clause or elementary node was created. The four steps are each below 2000 characters, and their calculations contain no hidden comparison lemma beyond the cited tensor-pullback compatibility. The two generic off-unit tools are explicitly declared in split_report.tool_uses, for properness permanence and monoidal pullback comparisons. Nothing remained unproved in this one-level split.

## Unfinished work

None at stage 1; the existing cited nodes retain their independent proof obligations.
