## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-pur-supported-tensor-isomorphism-transport.json`, the item, statement, now split. Mathlib verdict: no exact match or one-line specialization for the entire geometric normalization assertion. There are zero new nodes and zero Mathlib leaves. `citations.json` records a verbatim statement quotation for each of the fourteen step citations. `searches.jsonl` retains the actual Q82 search results.

Attachments: none. I searched the whole project `lean/WeilConjectures/` for the blueprint tag and supported/tensor/transport terminology, and narrowed the latter search to the pro-etale and six-functor directories. No declaration states this item exactly. The related ordinary module and supported quasi-coherent comparisons have different coefficient categories or assertions and are not attachments. No Lean was written or compiled.

WANTED: none.

The item had an empty proof, but its statement is correct and is unchanged. Its existing three substantive interfaces already supply all the non-elementary ingredients, so no supporting clause has been reissued as a new node. The original report/source descriptions are provenance, not mathematical dependencies. No false statement, ill-typed equation, or blueprint route error was found. I corrected no statement and changed no maintained metadata.

Nothing remains unfinished in the split. Independent maintainer review remains the normal next review after delivery.

## Sources and searches

I read the current blueprint's `sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`, especially the symmetry paragraph, and its current affine-space ancestor proof in `sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`. I also read the chapter and recorded unit and the current `sk-prop-an/_section.md`. The unit route stays fixed: this is the supported-open transport calculation used below the affine-space composition/symmetry argument, not a new purity proof.

I read Stacks `sites-cohomology.tex`, label `lemma-pullback-tensor-product` (Tag 07A4), and label `lemma-j-shriek-and-tensor` (Tag 0GL1), together with `sites-modules.tex`, label `lemma-j-shriek-and-tensor` (Tag 0E8I). These sources justify the existing general interfaces; none literally states the full transport result here. The proof is therefore expressly recorded as agent-written, using those existing interfaces rather than attributing the transport result to a Stacks tag.

Whole-blueprint searches for “supported tensor”, “open tensor”, and “tensor isomorphism transport”, plus DAG searches, found no blueprint statement equal to the item. The open external-tensor normalization node is narrower, concerning product opens and bounded finite-Tor inputs, and is not needed. The existing finite-open-product-swap node depends on this item; I read its statement and proof for the intended use but do not cite it, avoiding a cycle. The nearest blueprint ancestor was confirmed as `prop-pur-affine-space-composition-law`; the existing precise `from.place` and via chain are retained and `same_as` is empty.

Every added Mathlib search record is copied from the actual msearch log, with identical tool/query text. The two LeanFinder phrasings returned general homological tensor constructions or ordinary scheme-module restriction comparisons. LeanSearch returned zero-object and free-monoidal normalization results. The first Loogle query returned no hits; the second found `CategoryTheory.Adjunction.homEquiv_unit`, which I read with `homEquiv` in `Mathlib/CategoryTheory/Adjunction/Basic.lean:162` and the alias at line 181. This is a generic ingredient, not the item. The logged grep searches returned generic extension/triangulated statements and braiding/adjunction formulas; I also read braiding naturality in `Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`. These do not supply the specified ordinary unbounded pro-etale operations and their canonical comparisons in one specialization. No unavailable service was treated as a negative result. Earlier inherited search records were retained.

## Tool uses

`def-sf-finite-open-tensor-operations` supplies the actual operations and Cartesian comparison conventions. `lem-sf-open-tensor-normalization` supplies the generic unbounded open-adjunction unit, full faithfulness, invertible base-change map, and its unit normalization. Their use is declared in `split_report.tool_uses`; they provide generic tools and do not replace any geometric step of the purity unit. `lem-pur-derived-pullback-tensor-iso` is already in the item's unit and supplies finite-level naturality, composition and signed-symmetry compatibility.

## Not duplicates

No new node is proposed. The faithful-restriction calculation is a short proof step from the given supported isomorphism and the existing full-faithfulness theorem. Likewise signed conjugation is a step from naturality and involutivity, rather than a new node restating a conclusion of the item.

## Review by Q82

I checked delivery-errors B through E against the item, each cited node's full statement, and the sources above. The three interfaces are exactly `def-sf-finite-open-tensor-operations`, `lem-sf-open-tensor-normalization`, and `lem-pur-derived-pullback-tensor-iso`; quotations in citations.json are their full statements so the hypotheses as well as the used clauses remain visible. There are no new statements to source, search, or test independently. All steps are shorter than 2,000 characters.

Step 1 applies the normalization theorem with old open i', new open i, and maps g,h. I checked this orientation against its statement: beta goes from GJ' to JT, and theta goes from UG to TV. Its assertion about the adjunct of beta inverse yields the displayed formula with theta inverse and both units. The coefficient rings are the identical finite constant A with the canonical structural map, and the square is Cartesian, as required. The finite-open definition fixes precisely these comparisons and the section-normalized adjunction. No unspecified identification or arbitrary base-change isomorphism is substituted.

Step 2 uses the normalization theorem for beta invertibility and the finite clause of the pullback/tensor theorem for m and v. Functorial preservation of inverse pairs and composition are elementary. Invertibility of f' is an explicit hypothesis, so support is established before it is used for uniqueness.

Step 3 uses the operation definition for the Cartesian comparison and the tensor theorem's explicit naturality and composition clauses. I checked the domain and codomain of both sides of its first displayed equation: each runs from UG(E') to TV(R') tensor TV(H'). The second equation runs from U(E) to TP' tensor TQ'. This is a substitution of the cited coherence equations, not an independent assertion that all canonical maps commute. The finite theorem permits arbitrary unbounded inputs, and ell is invertible on every scheme here because they are k-schemes with ell different from the characteristic.

Step 4 uses only naturality of those specified comparisons, the hypothesis on Vf', and Step 3. I checked cancellation and units explicitly: U(beta) theta inverse T(eta') is eta at TD', then UJ(m) eta at TD' is eta at D followed by m. This derives the actual asserted equation for f rather than proving existence of a different normalized map.

Step 5 uses the normalization theorem's full faithfulness and invertible unit on the essential image of J. I checked that precomposition is by f inverse, whose domain is JD. Restriction then determines the unique interior maps t,s by unit naturality. For the reversed source the isomorphism to JD is f composed with sigma(H,R). Thus the same three-line argument applies for every D0; it makes no assumption that R or H separately is supported. This is elementary relative to the cited statements, and no standalone node for a clause of the item is introduced.

Step 6 uses naturality of the unit, naturality and involutivity of the defined signed symmetry, and the tensor theorem's signed-commutativity clause. I checked the order of the two symmetries: sigma(UR,UH) follows sigma(UH,UR), so they cancel. The two signs are (-1)^(rs) and (-1)^(sr), not a claim that either factor is individually even. The remaining expression is precisely the reversed unit equation. Step 5 with D0=Q tensor P gives uniqueness.

Step 7 uses the operation definition's actual pullback-composition/equality comparison under the identity unitors. The transported a,b and the original a',b' coincide under these identifications; the hypothesis and Step 4 are therefore the same unit equation. Step 5 proves equality with f', avoiding an additional unproved coherence claim about identity beta.

Small cases checked: i the identity (the supported-source argument reduces to ordinary equality); W empty (f forces its tensor source to be zero and all maps in question are unique); either tensor input zero; odd shifts of two degree-zero complexes (each swap has a minus sign but the pair cancels); and genuinely unbounded inputs. Arbitrary D0 is retained, with no support hypothesis on R or H individually. The argument uses no boundedness, constructibility, finite Tor-amplitude, geometric stalk conservativity, or exceptional inverse image. All non-elementary facts are statements of cited nodes; no proof of a cited node is used as an interface. No SGA source or excluded route is used.

The server-only preliminary review_split check exited 0 with PASS, zero new nodes, and the declared tool use accepted mechanically. The item's statement and maintained metadata were compared against the live repository and remain unchanged.
