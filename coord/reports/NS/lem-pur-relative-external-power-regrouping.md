# Stage-1 delivery: lem-pur-relative-external-power-regrouping

Group NS, 2026-10-22. Direct delivery under the dispatcher's brief.

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-relative-external-power-regrouping.json`: statement, split into four proof steps; no Mathlib match for the whole assertion.
- `citations.json`: a verbatim statement excerpt for each citation of each step.
- `searches.jsonl`: actual search-command log; all inherited item searches remain in the node and fresh searches are appended.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit record needed editing: this item is not the unit's key statement. All work was written in the prescribed sandbox; no Lean was written or compiled.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, external-product declarations and regrouping. Read `SixFunctors/ProEtale/FiniteCoefficient/Derived/ExternalProduct.lean` and the relevant signatures and proofs in `SixFunctors/Etale/Derived/Kunneth/Relative.lean`. The former defines the binary product. The latter has etale binary external-product pullback and compact-support comparisons, not every clause of this pro-etale iterated assertion (including geometric permanence and finite-Tor domains). They do not attach the item. An upstream declaration's absence of a local `sorry` would in any case not replace this signature comparison.

## WANTED

None.

## Corrections and scope

The item statement is retained verbatim. It was unsplit with an empty proof. Its source references give binary derived comparisons but not the needed induction or the finite-Tor domain argument. The split supplies both. No statement dispute was found. The parent product-domain result and relative-product geometric-factors result are not cited: the former depends on this item, and the latter asserts much more, including compact-support exchanges. In particular we avoid the large ctf-stability summary, whose unrelated Hom and exceptional-adjoint clauses require duality. Only the separate pullback and tensor preservation statements are used.

The nearest blueprint ancestor is `prop-pur-affine-space-composition-law`, through `lem-pur-affine-space-product-domain`. Read its current main-20261015 proof, especially Steps 3--4, and the recorded chapter and `sk-prop-an` unit route. This split makes the coefficient regrouping and domain checks available for that route; it does not alter the route or prove purity by a different route. Whole-blueprint searches for external power, regrouping and relative external found no equivalent blueprint statement. Searches for tensor-ctf and pullback-tor found the existing preservation lemmas, which were reused. Scheme-permanence and symmetric-monoidal searches and the whole-DAG keyword search similarly led to existing nodes. No new node was necessary.

## Mathlib search results

Ran the four requested search modes through the prescribed `msearch.py`, and a second grep phrasing:

- LeanFinder: iterated relative external derived tensor products of bounded constructible finite-Tor complexes; returned general categorical Tor definitions and complex tensor infrastructure.
- LeanSearch: derived inverse image preserving finite tensors and bounded constructible finite-Tor subcategories; returned finite-limit preservation of sheaf pullback and module/ring tensor functors, not the needed constructibility and Tor theorem.
- Loogle: `CategoryTheory.MonoidalCategory, "tensor"`; returned the general tensor functors.
- grep: `externalProduct|constructibleFiniteTor|boundedConstructibleFiniteTor|Kunneth`, AlgebraicGeometry: no hits.
- grep: `constructible|externalProduct|finiteTor|FiniteTor`, CategoryTheory: diagram external products and Day convolution. Read `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean`, the Tor definitions in `Mathlib/CategoryTheory/Monoidal/Tor.lean`, and tensor-category documentation. Diagram external products are functors on product index categories; they are not relative products of sheaf complexes on schemes. The first and second semantic phrasings and both grep phrasings therefore do not give a Mathlib leaf for the whole item.

Every fresh query is recorded exactly as run in the item and searches.jsonl. No service was unavailable in these fresh searches. Existing item search records were retained as inherited evidence.

## Not duplicates

No new nodes. Existing scheme base-change and composition nodes, the two finite-Tor preservation lemmas, the two canonical derived comparison nodes, the constant-ring comparison and the ringed-site monoidal theorem supply all inputs. Neither an elementary finite induction nor a clause of this item was turned into a new node.

## Review by NS

I read delivery-errors B--E against the node and sources, not just its dependency list. The item uses finite constant commutative coefficients A=O_E/varpi_E^n on small pro-etale sites, with compatible small skeletons as in the existing convention nodes. I read the statements of every node cited below. All citations in citations.json are actual contiguous passages from those statements.

For Step 1 I read Stacks schemes.tex, Tag 01KU, `lemma-separated-permanence` (composition and base change), and morphisms.tex, Tags 01T3 and 01T4, `lemma-composition-finite-type` and `lemma-base-change-finite-type`. The cited separated-base-change node states exactly that the pullback projection stays separated. The finite-type-composition-base-change node states both required finite-type closure properties. Clause (e) of proper-fp-permanence really does assert separated composition; the proof does not take finite-type composition from its weaker locally-finite-type clause. The fibre-product definition gives the actual square and its projection equations. The two projections have the two distinct base-change descriptions: a_j changes f_{j+1} along h_j, whereas b_j changes h_j along f_{j+1}. Composing h_j and the existing projections with a_j supplies the new structure map and old-coordinate projections. Composing with the structure map of B supplies separated finite type over k. Identities satisfy both properties directly. This is the needed induction, not an unsupported claim about arbitrary fibre products.

For Step 2 I read the current blueprint statement of lem-sf-pullback-tor-amplitude under main-20261015 and the statement and proof of lem-sf-tensor-ctf there, then compared them to their current DAG statements. Pullback really asserts both bounded constructibility and the same Tor interval, for separated finite-type maps of finite-type k-schemes. Those hypotheses have all been established in Step 1, and ell is invertible by the standing field datum. Tensor clause (ii) really asserts finite-Tor constructible closure, with interval addition, for two finite-Tor inputs. I specify the prefix induction and its initial object; thus no hidden finite-product stability lemma is used. The interval after s factors is the sum of their finite intervals. Finally pullback is applied to T_j only after its finite-Tor status is proved. Finite Tor amplitude of A-coefficients is not inferred from constructibility alone. No claim of geometric flatness is used.

For Step 3 I read Stacks sites-cohomology.tex, Tags 07A4 (`lemma-pullback-tensor-product`), 0G7E (`lemma-pullback-K-flat`) and 0D6D (`lemma-derived-pullback-composition`), including their K-flat computations. The tensor-pullback node states a canonical bifunctorial isomorphism on the unbounded derived categories of module sheaves, so it applies to the ambient images of the finite-Tor complexes. The composition node explicitly requires compatible inverse-image identifications of all three coefficient sheaves and supplies the canonical derived isomorphism with its termwise description. The constant-ring-map node says its map is an isomorphism with the unique constant-section-preserving identifications. These identify the composite coefficient maps because both fix every constant section, which verifies the composition node's extra hypothesis instead of assuming it. The distribution induction has identity as its one-factor base, then the binary tensor comparison followed by the induction map tensor identity. For the projection comparison the direction is the inverse of c_{a,p_i}: it goes from La^* Lp_i^* to L(p_i a)^*. This is the direction the item needs. These are derived-object isomorphisms, not per-degree claims.

For Step 4 I read Stacks Tag 0FPT, `lemma-symmetric-monoidal-derived`, and the full statement of lem-sf-ringed-derived-closed-symmetric-monoidal. Its tensor bifunctor and usual associativity constraints are exactly the ones used. A left-associated tensor makes the append step literal; other fixed parentheses are handled by the specified associators. No symmetry/permutation theorem, Hom formula or site-perfect duality conclusion is taken from it. Tensoring the explicit lambda_j with identity and appending the last coordinate gives precisely rho_j, so the proof establishes the map in the statement, not just the existence of some abstract isomorphism.

I tested r=1 (no regrouping comparisons), j=1 (single factor and only a composition component), zero input complexes, empty schemes and empty fibre products. Empty cases impose no nonemptiness or dimension hypotheses; constant coefficient sheaves on the empty scheme are covered explicitly by the ring-map node. The proof never identifies the projections a_j and b_j or assumes equal factors X_i. Binary tensor may be unbounded for general inputs, but each actual factor here has a finite Tor interval and tensor clause (ii) bounds the finite prefix before it is used.

I also checked that the cited non-elementary statements' dependency closures do not reach this item. Off-unit generic tools are declared, with their limited uses, in split_report.tool_uses. No new unsplit statement, hollow definition, uncited non-elementary assertion, renamed item clause or SGA source was introduced. All four steps are below 2000 characters; their inductions and coefficient compatibility checks are written out. The remaining verification is the required server dry run and delivery; no work on the mathematical split is outstanding.

## Unfinished work

None in this one-level split. The cited existing nodes retain their own independent proof obligations.
