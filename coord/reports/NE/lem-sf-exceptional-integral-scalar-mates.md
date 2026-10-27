# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-sf-exceptional-integral-scalar-mates.json`: statement, split into ten proof steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged. All 23 proof dependencies already exist.
- `citations.json`: verbatim statement evidence for every step/node pair.
- `searches.jsonl`: the actual search-command log. Original item searches were retained; this run adds LeanFinder in two phrasings, LeanSearch, Loogle, and two source grep searches.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiler invoked.

## Attachments

None. Searched the project source by the exact blueprint tag and by scalar/mate, completed-scalar and ramified-system terminology. The finite-coefficient restriction-scalar mate and ordinary module-object scalar square are partial results, not the integral exceptional construction. Read Mathlib's `mateEquiv_counit` at `CategoryTheory/Adjunction/Mates.lean:123` and `mateEquiv_vcomp` at line 170: these give generic categorical tools, not this item's geometric adjunction or completed scalar realization.

## Wanted literature

None. All sources needed here are available locally.

## Problems and corrections

The item had no proof. Its existing statement already includes constructible levels in the normalized-system category, the correction made in its parent's review; I retained that condition. There is no statement dispute and no change of hypotheses. In particular I did not add absolute separatedness of X or Y, or flatness of finite quotient coefficient maps.

The computed blueprint ancestor is `None`: the parent's maintenance `created.item` is a module name. This is the exact result of `tools/blueprint_refs.py ancestor lem-sf-exceptional-integral-scalar-mates`, already accepted in the parent review. I retained the null ancestor and existing via list, filled the place precisely, and searched the whole imported blueprint for cofinal systems and scalar mates. No blueprint node states the entire item in another form.

The tempting `lem-pur-compact-support-scalar-shift-normalization` assumes separated X and Y, so I did not use it. Instead the proof uses the slotwise integral-realization shift theorem and `lem-weil-completed-scalar-chain-shift`, both allowing the schemes in this item. Likewise `lem-weil-scalar-extension-composition` concerns rational categories, so it is not cited for integral composition; the proof uses ordinary sheaf-ring balanced associativity and the specified chi.

## Not duplicates

No new node is proposed. The cofinal-equivalence calculation is an application of the existing subsequence adjunction, normalization, and conservativity, not a new lemma. The composite counit calculation is written explicitly as an elementary proof step. All other required facts are cited from existing nodes; no clause of the item was relabeled as a new obligation.

## Review by NE

I read the complete item and the parent report's retained steps 13–16. I read Zheng's Construction 4.1 (printed p. 21), Lemma 4.10 and the normalization criterion 4.13 (pp. 23–24), Construction 5.15, Lemmas 5.16 and 5.22, Proposition 5.24 and Proposition 5.26 (pp. 35–37). They establish the intended route through actual coefficient systems and evaluated exceptional adjunctions, rather than an ambient pro-etale exceptional adjoint. I also read the integral paragraph of the blueprint exceptional-inverse-image definition, and Bhatt–Scholze 6.7.19 and 6.8.2(1), pp. 58–59. The coefficient sheaf is the completed sheaf; it is not silently replaced by a discrete constant integral ring. My proof is marked agent-written because Zheng does not state all the precise realization/shift normalizations in this item. Those additional facts are explicit existing DAG statements, not claims attributed to Zheng.

For step 1 I opened `lem-sf-exceptional-integral-reconstruction`, `lem-sf-exceptional-system-transport`, `lem-coef-derived-system-evaluation-calculus`, `def-weil-finite-tor-amplitude` and `lem-sf-integral-compactification-system-realization`. Reconstruction expressly supplies the reduction/limit equivalence and transported units and counits; system transport expressly identifies the evaluated units, counits and quotient transitions. The evaluation-calculus counit is the adjunct of the actual limit projection. Finite Tor amplitude makes literal reduction a valid restricted functor. The realization theorem intertwines the generator units/counits and tensor/open maps. Thus this step does not ask a definition to supply a missing adjunction or a missing comparison theorem.

For step 2 I read the complete statement of `lem-pur-system-level-left-extension`, including its formula with t(m), its selected-level transition and its conservativity assertion. Restriction has the left adjoint used in the proof. At m=en its unit is a tensor unitor; the counit at m is exactly the normalized transition from e t(m). These explicit maps prove equivalence, using joint detection of isomorphisms only. For constructibility of the inverse extension I use `lem-sf-exceptional-finite-scalar-mates`, whose hypothesis permits the finite quotient A_{L,en} to A_{L,m} without flatness and whose statement preserves the Tor interval. Tensoring with a degree-zero module tests the same interval on the selected input; setting that module to the coefficient ring gives a common cohomological bound. This is a few-line application of existing statements, not a hidden cofinality theorem or an appeal to faithfulness of evaluation.

For step 3 I opened the ordinary etale system adjoint, system coefficient projection, system scalar-mate coherence and cofinal-mate nodes. The adjoint node supplies the finite-free comparison at R_L/varpi_E^n, including quotient and associator compatibility. The projection and scalar-mate nodes give q and invertible b as transformations of entire systems with the displayed counit equation. The cofinal-mate node permits nonseparated Y and identifies the restricted right adjoint by a counit-preserving Hom calculation. The system-transport node moves the adjunction through etale/pro-etale comparison. The realization theorem includes system tensor expressions and their generator maps, so applying it to finite-free coefficient tensor identifies the same scalar arrows. All these hypotheses hold for the fixed compactification of the separated finite-type morphism, without assuming X or Y absolutely separated.

For step 4 I read `lem-weil-finite-free-completed-scalar-comparison`, `lem-weil-integral-scalar-extension-constructible` and `lem-pur-adic-scalar-extension-tor-bound`, and the defining strict-tower scalar functor. The first states that its specific chi is a natural isomorphism on derived-complete inputs, not just that another functor is isomorphic. The second supplies constructibility, and the third tests every L-level m through an E-level n with en>=m and preserves exactly the Tor interval. This verifies the restriction and theta=chi^{-1}. No flatness of A_{L,m} over A_{E,n} is used.

For step 5 I re-read the map clauses of integral reconstruction and compactification-system realization and the open-tensor normalization. The realization maps intertwine units, counits, tensor/pullback maps and whiskered generator maps on bounded normalized expressions. The integral left functor has exactly the prescribed realization by reconstruction. The finite-free scalar functor fits these expressions as tensor by the coefficient system. Conjugating the system counit identity therefore gives the stated equation for the chosen integral functors. The open normalization identifies its inverse as the open-unit adjunct. This pins down the actual ambient proper/open scalar map, not merely its finite evaluations.

For step 6 I checked the exact hypotheses of `lem-pur-integral-realization-shift-coherence`: the inputs and all intermediate expressions have etale-origin witnesses and common constructible/Tor bounds supplied by the given reconstruction. Its statement includes the generator maps and the canonical termwise/Roos shifts. The completed-scalar-chain-shift node applies to any scheme, specifies the (-1)^r second-cone-coordinate sign and says that the quotient comparison preserves it. Adjoint-shift uniqueness supplies the right shift; the counit equation determines the shifted b. The commshift composition/whiskering node supplies the formal closure properties used here and in step 10.

For step 7 I read the balanced derived quotient-normalization and scalar-unit nodes. Their representative maps are exactly (x tensor s) tensor t -> x tensor b(s)t and x tensor r -> rx. They apply to arbitrary sheaf-ring maps, so mixed quotients cause no extra flatness requirement. The category inclusions are full by the item's definition. Consequently conjugating and lifting these actual ambient natural isomorphisms supplies scalar identity/composition with the required realized maps. I checked the Stacks texts for Tags 0D6D (lemma-derived-pullback-composition) and 0G7E (lemma-pullback-K-flat), not a mutable section number.

For step 8 I read `lem-pur-ringed-coefficient-projection-cocycle` in full. It states the proper scalar cocycle, identity, canonical shifts, and its strict-system version before evaluation or limit. I also read Stacks Tag 0E47 (remark-compose-base-change-horizontal), whose omitted verification is not substituted for the existing DAG cocycle theorem. The open-normalization node supplies the open-adjunction characterization on arbitrary ringed diagram sites. The two open composites have the same restricted tensor map; the adjunction bijection proves their equality. The realization generator clause then preserves this same equation. No off-route geometric theorem replaces the unit route.

For step 9 I type-checked the displayed counit product: it starts at V_Y T_Y F_s G_s and ends at V_Y T_Y. Naturality moves F_u V_X(b_a) across q_c; the counit equation for c and then the equation for a reduce the product to V_Y T_Y(epsilon_s). These are substitutions and the adjunction bijection, so elementary=true is justified. There is no asserted general fact that mates of arbitrary isomorphisms are automatically invertible: generator invertibility comes from the cited system comparisons and composite invertibility from composition.

For step 10 I checked the balanced-associator shift node, the commshift node, and the induction on generators, identity and composition. This introduces no new existence theorem. All necessary comparisons are already constructed; their realized left map and right counit transpose are fixed by steps 8–9.

I checked small cases: the zero complex; the identity field extension and its nontrivial published completion functor (unitor via chi); unramified e=1; ramified e=2 at m=1,2,3 (selected indices 2,2,4, never relabeled as 1,2,3); quotient maps with infinite projective dimension over the source; n=1; and empty schemes, where the functors are zero and no dimension assertion enters. With n>=1 the minimum t(m) always exists. Every cited statement was opened and is quoted verbatim in citations.json. I checked the dependency closure of each candidate citation for dependence on this item; none depends on it. No proof step exceeds 2000 characters. No SGA source is used.

The off-unit citations are foundational system, coefficient, realization or shift tools. They are declared in `split_report.tool_uses`; each supplies a generic interface this unit does not replace. No top-level tool approval was added. Sections B–E were checked against the concrete files: self-contained unchanged statement, exact sources and maps, no new duplicate or hollow node, all non-elementary inputs cited, no circular citation, no additional geometric or flatness hypothesis, and no missing composition argument.

## Unfinished work

None for this one-level split. Existing unsplit dependencies remain their own stage-1 items. No claim of a finished Lean proof is made.
