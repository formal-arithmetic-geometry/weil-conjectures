## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-normalized-comparison-binary-restriction.json`: unchanged statement, seven explicit elementary calculation steps, proof dependencies, agent proof provenance, and newly run Mathlib searches appended to the inherited searches.
- `citations.json`: a verbatim statement quotation for every node used by every proof step.
- `report.md`: this report.

New nodes: none. New Mathlib leaves: none. The existing leaf `lem-amb-natural-transformation-whisker-exchange` supplies precisely the naturality exchanges needed. The category definition leaf supplies associativity. No Lean file was written, no compilation was performed, and no unit or chapter was changed.

Attachments: none. Searches for the exact blueprint tag, normalized comparison/restriction terminology, and binary comparison terminology under `lean/WeilConjectures/` did not find a declaration stating this item. The normalized-tower declarations in `SixFunctors/Etale/Derived/IntegralCoefficients.lean` and `NormalizedTowerRealization.lean` concern coefficient towers, not arbitrary categories with the supplied restriction and extension functors. None was treated as a finished proof of this item.

WANTED: none.

The imported node had no proof. Its hypotheses and both conclusions are correct; no STATEMENT-DISPUTED or statement correction is needed. Its creation/source metadata and all inherited searches were retained. The source is already explicit that this is an agent-extracted formal calculation rather than a Stacks theorem. Its proof is accordingly marked `proof_origin.by = agent`, with the current blueprint as motivation. There is no direct theorem in the cited blueprint that has been mistaken for this abstract calculation.

Unfinished work: none at the requested one-level stage-1 split. All seven steps are short substitution or naturality calculations; there are no new unsplit obligations.

## Sources and searches

Read the current `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-prop-scalar-six.json`, and `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md`, especially paragraph (2)'s final sentence. This split supplies only the abstract binary normalization subargument used by the parent coherence node, and preserves the unit's extension-by-zero comparison route. It does not assert the projection formula or existence of geometric comparisons.

Read Stacks `categories.tex`, Tag 001B (`definition-functor`), for preservation of identities and composition, and Tag 001I (`definition-transformation-functors`), for the component naturality square, componentwise composition, and interpretation of equality of natural transformations. Read the complete statement of `def-nagata-category` (Tag 0014, `definition-category`) and the complete statement of `lem-amb-natural-transformation-whisker-exchange`. Verified the latter's Mathlib match directly in `Mathlib/CategoryTheory/Whiskering.lean`, lines 203--207. These are the only external categorical tools used.

Searched the entire DAG for natural-transformation/whiskering statements and the entire imported blueprint using `tools/blueprint_refs.py search` with `naturality`, `normalized comparison`, `restriction normalization`, and `whisker`. The specific exchange law already has a Mathlib leaf; no duplicate is created. No imported blueprint node found by these searches states both clauses of the item. The item's existing precise `blueprint.from.place` and `same_as: []` remain appropriate.

The five new queries in sandbox `searches.jsonl` were all executed through `msearch.py`: LeanFinder with two phrasings, Loogle, Mathlib grep, and LeanSearch. All services returned results. Their actual logged records are appended verbatim as the new `mathlib_searches` results. Read the returned names/types and inspected the plausible general hits: `CatCommSq.hComp`/`vComp` at `CatCommSq.lean:70,87` construct isomorphisms for squares, `hInv`/`vInv` at lines 108,149 require equivalences, `NatIso.hcomp` at `NatIso.lean:209` constructs a horizontal composite, and `Adjunction.comp_counit_app` at `Adjunction/Basic.lean:580` assumes adjunctions. None states the two conditional normalization identities under this item's arbitrary data. The primitive whiskering identity is reused through the existing leaf, so this is not a Mathlib leaf merely because its several calculation steps use naturality.

## Not duplicates

No new nodes were created. In particular, the elementary substitutions were kept as proof steps and the existing exchange law was cited instead of introducing another naturality lemma.

## Review by Q08

I read the item's exact statement, the parent coherence node, paragraph (2) of the current blueprint proof, the unit's route, and the categorical sources listed above. No SGA source is involved. There are no new node statements to review. The item assumes the two individual normalization equations (N), the two compositor equations (G), and the formula for the composite restriction comparison. The proof uses these as hypotheses, not as conclusions imported from a definition node.

Step 1 uses the actual exchange formula in `lem-amb-natural-transformation-whisker-exchange`: take its inner transformation to be h_b and its outer transformation to be rho_a^s. This gives precisely rho_a^s at the target of u, followed by L_a^s E_a^s(u), equal to u followed by rho_a^s at its source. The expansion of eta and H and the application of L_b^s then require only functoriality. Step 2 substitutes (N) at a with P=E_b^r M and at b with M. The cited category node says associativity, the only category law used to regroup these explicit equations; it is not cited as a theorem about normalization.

Step 3 uses the same exchange leaf with inner transformation rho_a^r E_b^r and outer transformation q_b. Its component is explicitly written, with v a morphism in C_S^r. The source and target functors of q_b are L_b^s F_S and F_T L_b^r, exactly the functors that can act on v. Step 4 substitutes this equation, combines adjacent F_T images, and recognizes the given definition of eta^r. The resulting component is literally the right-hand side of (B). Its cited category node supplies reassociation; component equality is the definition of equality of the families in Tag 001I.

Step 5 expands the specified tilde h, uses (G) for s at F_T M, and substitutes the just-proved (B). It uses the hypothesis defining q_ab, rather than assuming an unproved compatibility of arbitrary comparison maps. Step 6 uses the exchange leaf a third time, now with inner transformation gamma_r inverse and outer transformation q_ab, under the supplied restriction identifications. I checked that w_M is in C_X^r, the domain of q_ab, whereas the v used earlier was in C_S^r. This is the exact naturality substitution often concealed by the phrase 'transport along compositors'; it is fully displayed here.

Step 7 uses (G) for r and the actual inverse equation gamma_r composed with gamma_r inverse equals the identity on E_ab^r M. The order is important: eta^r composed with D^r(w_M) is rho_ab^r, not a cancellation in the opposite category. Functoriality and the category laws give the displayed calculation. The final natural-isomorphism claim is justified by explicit reversed inverses for composites and functor images of the inverse equations. No faithfulness, adjunction, exactness, geometric condition, or extra smallness hypothesis enters any step.

For B/C/D of the delivery checklist: the two cited node statements were opened and supply exactly the formulas quoted in `citations.json`; all other operations are one or two substitutions of hypotheses, functor laws, or definitions in each step. All steps are shorter than 2000 characters. No mathematical claim was moved into a new node, no clause was restated as a lemma, no source proof was used beyond a cited node's statement, and there is no cycle because both dependencies are existing Mathlib leaves. The argument uses only the statement's named functors, isomorphisms and equations.

For E and small cases, I checked the component types before each substitution. If C_T^r is empty, both conclusions are equalities of empty component families and the calculation imposes no nonexistent object. For all categories terminal, every equality is the unique identity. If a and b are identity-shaped data, the argument still allows the supplied nontrivial normalization isomorphisms and uses (G)/(N), rather than silently replacing them by identities. With nonfaithful restriction functors, the proof continues to compute only the requested restricted equality; it never cancels a restriction functor. These checks explain why the imported 'no faithfulness, adjunction, or geometry' clause is preserved. No statement correction or mathematical return repair was necessary.
