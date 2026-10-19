## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-interchange-proper-pasting.json`: statement, split; seven proof steps. The statement and inherited ancestry are unchanged. All new searches find no exact Mathlib match.
- `citations.json`: 15 entries quoting the current statements used in the seven steps.
- `report.md`: this report. `searches.jsonl` retains the search-command log; `prepare.py` is a sandbox-only preparation script, not a delivery node.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The derived restriction comparison used here is obtained by applying an existing underived comparison termwise to K-injective representatives, using existing K-injective preservation and exact-functor descent nodes. The compatibility required in step 5 is then a degreewise section identity on those same representatives. These are written out as short steps, rather than introducing duplicate or elementary helper nodes.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id, interchange, proper/open exchange and the relevant derived files. The exact blueprint tag does not occur. I read `SixFunctors/Etale/Derived/OpenImmersionLowerShriekLowerStarExchange.lean`, including the exchange definition at lines 97ff and its torsion-coefficient isomorphism theorem at lines 149ff. Its categories are derived categories of sheaves on small etale sites with a fixed abelian coefficient category; it does not state this comparison equation for module objects over pulled-back rational condensed rings on pro-etale sites. No attachment is claimed. The upstream master remains reference material only.

## WANTED

None. The blueprint and the Stacks sources needed for this split are present locally.

## Findings and changes

The imported item was statement-only. No mathematical error or statement dispute was found, and no hypothesis or conclusion was changed. In particular the equation is an equality of maps on the whole ordinary unbounded module derived category. It does not assert that the interchange maps are isomorphisms on that category. The proof never invokes the constructible/localizing isomorphism clause (3) of `det-sf-comp-composition-interchange`.

I read the chapter record `sec-six-functors-basics`, the inherited unit `sk-cor-affine-space-rational`, and the current blueprint composition proof, especially the first two sentences of “Canonicity and associativity”. The item is a subordinate proper-map pasting obligation in the lower-shriek composition used for exceptional inverse-image composition in the affine-space unit. Its inherited unit and blueprint ancestry were retained; the auxiliary generic tools are declared under `split_report.tool_uses`.

The key potential gap is the word “canonical”: uniqueness alone cannot compare two composites until their restriction identifications are known to agree with the specified derived direct-image comparison. Steps 2–5 address this explicitly. In particular, the normalization of `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is used on representatives for which the intermediate direct images are already K-injective. The comparison is therefore the actual termwise composition identification, not an arbitrary isomorphism of right adjoints.

## Searches and reuse

The complete imported search record was preserved. Five additional searches were actually run through `msearch.py`, and their exact tool/query texts are appended to the item and recorded in `searches.jsonl`: two LeanFinder phrasings, Loogle `"mate", "comp"`, grep `interchange|extensionByZero|lowerShriek` in `CategoryTheory`, and LeanSearch for the normalized proper/open vertical composition statement. All five services completed. Generic mate-pasting hits, condensed-module naturality, underived `SheafOfModules.pushforwardComp` and scheme-module restriction/composition do not supply the specified pro-etale unbounded condensed-module comparison. I read the returned underived pushforward component formulas and associativity in Mathlib's `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`, lines 145–173, and the conjugation material in `CategoryTheory/Adjunction/Mates.lean`, lines 310–350. No exact or one-line-specialization Mathlib leaf for this item is asserted.

I searched the whole DAG for interchange, restriction/composition, mate-pasting and the Stacks places 0D6E and 0F7C, and ran `blueprint_refs.py ancestor` plus whole-blueprint searches for `interchange`, `mate`, `restriction`, `restriction.*pasting`, `ringed.*exchange`, `proper.*pasting`, and `interchange.*successive`. The precise proper-open interchange node was reused. I opened the nearby `lem-cbc-proper-open-interchange-coherence` and `lem-exc-proetale-derived-open-restriction`: the former has bounded-below etale finite coefficients, the latter finite constant pro-etale coefficients. Neither can be used for this rational condensed-ring claim. Instead the existing `lem-sfb-proetale-open-restriction-counit` explicitly allows an arbitrary ring sheaf. No new node was necessary.

## Not duplicates

No new nodes. The existing finite-coefficient pasting and restriction statements were not silently generalized; their coefficient hypotheses are why the proof uses the arbitrary-ring restriction statement instead.

## Review by Q86

I reviewed the seven steps against the item, the node statements, and the source texts, with the coefficients and the directions of all comparisons visible. For the item I read the current main-20261015 composition proof, “Canonicity and associativity”, first two sentences, and the proof and statement of `det-sf-comp-composition-interchange`. I also read Stacks `sites-cohomology.tex`, Tag 0D6E, label `lemma-derived-pushforward-composition`, and Tag 08FI, label `lemma-restrict-K-injective-to-open`, including the discussion of exact restriction and extension just before the latter; and `derived.tex`, Tag 08BJ, label `lemma-adjoint-preserve-K-injectives`. There are no new node statements to audit against additional sources. This is an agent-expanded blueprint argument, recorded with `proof_origin.by = agent`, rather than a claim that Stacks states this exact condensed-coefficient pasting theorem.

1. Step 1 uses the actual clauses (1) and (2) of `det-sf-comp-composition-interchange`: the inverse image of the lower open is the dense upper open, and the unique normalized map exists for every unbounded input. The two proper maps and quasi-compact dense opens in this item are precisely those hypotheses. Applying this successively gives the outer open as well. The outer maps and their normalized comparison are already the third configuration in the item's statement. I did not cite the constructible isomorphism assertion.

2. Step 2 uses the underived module adjunction stated in `sk-def-sfb-module-pushforward-pullback`, the exactness and inverse-image coefficient description in the last assertion of `sk-prop-sfb-cartesian-coefficients`, and clause (1) of `det-sf-open-closed-sequence-ring-sheaf`, which states exact open functors, their adjunction and the invertible unit. These are exactly the hypotheses of the cited right-adjoint K-injective preservation statement: use direct image as right adjoint to exact module pullback, and open restriction as right adjoint to exact open extension. The schemes are separated finite type over a field, hence qcqs, and the three opens are quasi-compact as required. There is no erroneous assertion that open extension preserves K-injectives.

3. Step 3 uses `lem-sfb-proetale-open-restriction-counit` for its actual restriction isomorphism and section formula, not for a theorem inferred from its name or proof. Its statement allows any commutative ring sheaf and identifies the two evaluations on the same fibre product. The inverse-image coefficient rings required there are identified with the chapter's pulled-back rings by the untwisted coefficient theorem. This is valid for E and for the finite-subextension condensed algebraic closure; I did not replace the latter by all continuous functions into the algebraic closure or by a constant ring sheaf.

4. Step 4 uses the existing exact-functor descent statement for its explicit termwise representative assertion and `sk-def-sfb-module-derived-pushpull` for total right derived images computed on K-injectives. With the preservation already proved in step 2, applying the isomorphisms from step 3 to a representative immediately produces the three natural derived restriction isomorphisms. This is a routine application of these cited statements, not an additional assumed derived base-change theorem or a new node hidden in a long step.

5. Step 5 uses the actual normalization clause of the ringed-topos derived pushforward-composition node: the class of the map obtained from a resolution of the intermediate direct image. Here those direct images are K-injective by step 2, so the resolution can be the identity. The other cited statement specifies the fibre-product section identifications. I checked both paths at an arbitrary pro-etale test object over Y: both are the same map on the complex evaluated at `W'` times that object over B, identified with `P'` times the object over Y. This is an equality of the actual component maps, with the same coefficient actions, so it survives localization with the required kappa direction. The proof explicitly gives the degreewise calculation; it does not quote finite-coefficient pasting or hide a new comparison theorem.

6. Step 6 uses clause (2) of the interchange node for the two normalized maps and clause (1) of the open-module node for the inverse units. I checked the types: X is Rh_*A on P, the source unit is at Rp_*X on Y, rho_s has target Rh_*v^*, and t_A is the inverse open unit v^*v_!A to A. Naturality of rho_r moves Rr_*(J_A) across restriction, after which the J normalization cancels eta_u and the I normalization leaves the identity. This is the displayed three-line substitution, with no invertibility assumed for I or J.

7. Step 7 uses naturality of precisely the specified kappa and then the uniqueness clause for the outer configuration. I checked the two compositions with kappa and its inverse: G_A has source i_!R(ph)_*A and target R(rs)_*v_!A, so uniqueness applies directly to G_A and I'_A. The extra source unit is moved by its naturality, and the displayed equation is conjugation of the identity, hence the identity. Rearranging G_A = I'_A gives exactly the equation of the item, including the inverse kappa inside i_!. Naturality in A follows from naturality of every displayed factor.

For B1–B10 and C1–C8, there are no new or renamed notions, no unsplit node carrying a proof, no uncited non-elementary theorem, and no manufactured search record. Every `uses` entry has a verbatim statement quotation in `citations.json`; I generated these by slicing the current statements and checked that each slice is actually present. The proof-dependency list is their union. The generic off-unit tools are explained in `split_report.tool_uses`, leaving maintainer-owned `tool_uses` untouched. I did not change any existing dependency node or maintainer metadata.

For D1–D5, the proof carries the normalization and section calculations itself; no new node restates a clause or receives the whole argument. For E1–E7, I checked arbitrary unbounded inputs, the actual pulled-back coefficient rings, and the exactness needed for K-injective preservation. I tested A = 0, an empty upper open, and identity proper maps: all formulas reduce to identities on zero or to the open-unit identities. If i is the identity, density and properness identify W with P, and likewise W' with P'; the equation reduces to the specified direct-image composition identifications. These checks do not exclude any such cases. No false statement, source error, or extra hypothesis was found. Each step has fewer than 900 characters, and the component calculation and normalization substitutions contain no unextracted long lemma.

No second worker was used: this is the direct-delivery self-review authorized in the brief. The maintainer's independent review remains the next mathematical review.

## Unfinished work

None in this one-level split. The existing cited nodes retain their own proof work; no unsupported completion or Lean attachment is claimed. Remote dry-run and delivery results are recorded after the required tools finish.
