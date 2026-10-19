# Q16: lem-pur-trace-transpose-base-change

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-trace-transpose-base-change.json`: existing statement node, now split into four steps; not a Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every citation in every step.
- `report.md`: this report. `searches.jsonl` is the search command's actual log; `write_split.py` is sandbox-only preparation code.

No new nodes and no new Mathlib leaves. The item statement and its existing statement dependencies are unchanged. No unit, chapter, Lean, live-project or launcher file was written.

## Attachments

None. Searched the entire read-only `WeilConjectures/` source for the blueprint id and for trace/baseChange and transpose/baseChange combinations; there was no hit. Also read the relevant exceptional-adjoint and dualizing declarations in `SixFunctors/Etale/Derived/UpperShriek.lean` and `Dualizing.lean` and searched the exceptional/smooth-duality files for counit, transpose and base change. They do not state this comparison. In particular, an adjunction definition is not an attachment of the claimed naturality identity. No master sorry declaration is used as evidence of completion.

## WANTED

None. The formal adjunction source is available locally as Stacks `categories.tex`, Tag 0037, label `definition-adjoint`, especially the paragraph characterizing corresponding arrows by the counit. Tag 0038, `lemma-unit-counit-relations`, supplies context for that characterization. No unavailable literature is needed.

## Audit and corrections

The imported item had no proof. Its statement already specifies the right finite, ordinary constant-module categories and the actual constructible exceptional Hom bijections. I retained it without a statement dispute. In the current parent split, the historical “Expanded Step 3” comparison is numbered Step 5: its equation is `J = B composed with Lp_2^*P`. The current main-20261015 parent proof discusses agreement of the diagonal/DNC orientation and the integration orientation; this item's calculation supplies only that formal transpose comparison, without replacing any diagonal or deformation argument.

I read the chapter and unit records, both the current blueprint parent proof and its current DAG proof, the compact-support exchange definition and finite-level theorem in the older source files, and the current main-20261015 ambient-adjoint proof. The detailed DAG statements have since clarified the ordinary finite coefficients and bounded etale-origin domains; those clarifications are respected here.

The calculation requires neither smoothness nor invertibility of the dualizing base-change map B. It only inverts C_L and C_omega, whose invertibility is already supplied by the compact-support theorem named in the statement. This avoids turning cohomological smoothness, a property not assumed here, into an implicit hypothesis.

## Mathlib and duplicate search

Searched the whole DAG by homEquiv/counit naturality and adjoint-transpose terminology and searched the whole imported blueprint with `blueprint_refs.py search adjunction` and `search transpose`. Ran `blueprint_refs.py ancestor` as well. Reused the existing Mathlib leaf `lem-weil-pbc-adjunct-counit-identity`; its statement is precisely the inverse-transpose counit identity. Other transpose comparisons found in the DAG impose site-comparison, coefficient-comparison, smoothness or ambient-adjoint data and are not this square. No equivalent blueprint node was found, so `same_as` remains empty. No new nodes need pairwise duplicate explanations.

The item's original search records were preserved. Additional searches actually run by msearch.py, with the two adjunction/mate phrasings, found `CategoryTheory.mateEquiv_counit` and the Hom-equivalence naturality lemmas. I read Mathlib `CategoryTheory/Adjunction/Basic.lean`, including homEquiv at line 160, its naturality lemmas at lines 226ff, and `eq_unit_comp_map_iff` at line 301; and `CategoryTheory/Adjunction/Mates.lean`, including the mate formula and `mateEquiv_counit` at line 123. These give the generic counit and mate identities, rather than the entire geometric assertion as a single direct specialization. The explicit naturality/substitution calculation is retained in the item's steps. LeanSearch's trace and dual-base-change results concern linear maps and do not state the compact-support comparison. The grep query had no hits. Every service returned a valid result; no failed search is described as a negative result.

## Tool uses

`thm-sf-ambient-adjoint-class` is used as the generic actual Hom-bijection infrastructure; `thm-cbc-finite-level-proetale` is used as finite compact-support exchange infrastructure. Both uses are declared in `split_report.tool_uses`. The Mathlib adjunct-counit identity is already a leaf; the other citations are definitions. This does not replace any step of the smooth-purity unit's route.

## Review by Q16

I checked the two directions and domains of every displayed arrow against the statements actually cited. For Step 1, `thm-sf-ambient-adjoint-class` explicitly supplies natural bijections on bounded-below etale-origin inputs, including bounded constructible inputs; `def-weil-exceptional-inverse-image` explicitly restricts the finite functor to D^b_c. Thus the dualizing objects in the hypothesis belong to that constructible category, and the unit coefficient object and the specified transposes lie in the actual Hom-bijection domains. The statement already stipulates the exchanges at L and omega and the f' transpose. There is no unrestricted ambient pro-etale exceptional adjunction hidden in the notation. The existing Mathlib leaf states both directions of the counit characterization, so it gives epsilon F(P)=t and epsilon' F'(B)=u U(epsilon) C_omega^{-1}; the latter is exactly the definition of B in `def-pur-co-smoothness`. I use only that map's construction, not any of the three cohomological-smoothness conditions.

For Step 2 I read the full formula in `def-cbc-exchange-map`: the unit, square identification, counit and open-extension comparison are natural transformations. Their composite is natural, and conjugation by the comparison isomorphisms retains that naturality. `thm-cbc-finite-level-proetale` identifies the exchange as this transported map and states invertibility and witness independence. Hence the naturality square at the actual morphism P, rather than at an unrelated trace, is available. The inverse equation has the correct order: C_omega^{-1} F'(V(P)) = U(F(P)) C_L^{-1}. This step is elementary composition/cancellation of the specified natural transformations; no hidden new geometric lemma is being asserted.

In Step 3 each equality is written out. Its third line uses exactly that inverse naturality equation; its fifth uses the first counit equation; its final line uses precisely the hypothesis t' C_L = u U(t), followed by right composition with C_L^{-1}. The comparison u is retained throughout, so the unit pullback is not silently treated as a literal equality. There are no new non-elementary facts in this substitution step. In Step 4 the same actual Hom bijection and the same existing counit leaf give uniqueness of the transpose, so equality of inverse transposes is enough to conclude the exact desired equality of arrows.

I tested identity base change, f the identity, t=0, L=0, and empty source: the displayed equations reduce to the usual identity or zero equations. The calculation also works when B is not invertible, as the statement requires. I checked the existing dependency closure of all six cited nodes; none reaches this item, so these citations introduce no cycle. Every non-elementary input has a named citation, every citation's quote was copied from its statement, and the proof contains no step over 2000 characters hiding an auxiliary lemma. No statement-only node, new coefficient category, duplicate, or restatement-child was introduced. The proof origin is marked agent because I wrote this formal calculation from the available adjunction characterization to expand the blueprint comparison.

## Unfinished

No mathematical work on this split remains. Its existing dependencies retain their own states; this delivery proves no claim about their Lean completion.
