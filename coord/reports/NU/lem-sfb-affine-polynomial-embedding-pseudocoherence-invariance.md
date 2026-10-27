# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance.json`: split statement; four proof steps; no Mathlib match.
- `citations.json`: nine verbatim statement excerpts, one for each node used by each step.
- `report.md`: this report. Search tooling also recorded its five actual searches in `searches.jsonl`.

No new nodes; zero Mathlib leaves. The sandbox initially contained only dispatcher brief markers, with no prior item, report, citations or searches to recover. The live item was unsplit and had no repair note.

## Attachments

None. Read-only searches in `lean/WeilConjectures/` for the item id and its blueprint tag, and for polynomial/presentation/embedding in pseudo-coherence contexts, found no declaration stating the complete finite-stage embedding-independence result. Nearby affine flat finite-presentation and stalkwise pseudo-coherence results impose different hypotheses and do not attach this item. No Lean was written or compiled.

## WANTED

None. All sources needed for the split are present in the read clone.

## Corrections and scope

The original statement is correct against Stacks Tag 09VC, `more-morphisms.tex`, `lemma-relatively-pseudo-coherent`. Its proof and proof dependencies were empty. The statement and its statement dependencies are retained exactly. In particular there is no added quasi-coherence, boundedness, Noetherianity or finite-presentation assumption. The finite type assumption is retained although the construction starts from the two supplied embeddings.

The existing ring-level `lem-sfb-polynomial-presentation-pseudocoherence-invariance` is insufficient as a replacement: it states the all-degrees property for an object of D(A), whereas this item fixes an integer m and allows a complex of arbitrary module sheaves. The split follows the source's geometric graph argument instead. The actual affine pseudo-coherence criterion is applied only to the pushed-forward structure modules of the two graph embeddings. It is never applied to the arbitrary complex E.

The inherited blueprint ancestor is null, as confirmed by `tools/blueprint_refs.py ancestor`; its detailed provenance and via list are retained. Read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md`, `sk-thm-sf-ctf-stability/_section.md`, and its direct-images proof, particularly paragraph (3). This is a supporting commutative-algebra/ringed-space input below the existing route, not a replacement for a unit-level step. The item is not a unit key node, so no unit realization file was changed.

## Not duplicates

No new node is created. Whole-DAG searches for 09VC, 09VA, 08E7, closed-push-pseudo-coherent, polynomial graph/evaluation and Koszul resolution found the existing inputs reused here. Whole-blueprint searches with `blueprint_refs.py search` for pseudocoher, pseudo-coherent, closed push and polynomial graph found no equivalent blueprint node. In particular `lem-trf-polynomial-graph-coinduction` already states the exact finite-free evaluation resolution required here; creating a graph-resolution or graph-structure-pseudo-coherence node would duplicate its elementary consequence with the existing affine criterion.

## Mathlib searches

Preserved the imported search records, and ran five new searches through the mandated `msearch.py NU <item>` command: LeanFinder with the item's statement and a second phrasing about adjoining/lifting polynomial generators, Loogle for PseudoCoherent and pushforward, Mathlib grep for pseudo-coherence/IsMPseudoCoherent, and LeanSearch for finite-degree embedding independence. Read every returned hit. The semantic services returned ordinary finite morphism/finite-type transition or finitely presented sheaf statements, not the derived m-pseudo-coherence assertion. Loogle and Mathlib grep had zero hits. All five completed successfully; no unavailable service was represented as a negative result. Exact queries and returned summaries are included in the node and preserved in the tool log.

## Review by NU

I checked the B--E return cases against the statement, all four steps, the live statements of all nine cited nodes and the relevant source passages. There are no new nodes needing separate statement-only, source-tag, blueprint, or Mathlib-leaf checks. The file remains one JSON node with single TeX escapes. The result is an argument through two evaluation embeddings, rather than replacing the item by a node that asserts its conclusion.

For step 1, I read the full affine clause of `def-nagata-relative-affine-space` and the affine-surjection characterization in `def-weil-closed-immersion`. These give exactly the polynomial rings and surjections used. Surjectivity supplies the finitely many lifts f_b and g_a; the two composites agree on R, every x_a and every y_b, so they are the same ring map. Each evaluation map is surjective because it is the identity on its coefficient polynomial ring. Its spectrum is therefore closed by the cited definition. This short coordinate construction is elementary and agrees with the two diagrams in 09VC.

For step 2, I read `lem-trf-polynomial-graph-coinduction` and used only the sentence explicitly asserting the bounded finite-free resolution of an evaluation module. Substituting A=P, added variables y and evaluation values f gives a T-resolution of P; substituting A=Q, added variables x and values g gives a T-resolution of Q. The statement allows arbitrary commutative rings and zero variables. I also read `schemes.tex` Tags 01HV (`lemma-spec-sheaves`) and 01I9 (`lemma-widetilde-pullback`), and the full live statements of `lem-weil-pbc-spec-tilde-free-module` and `lem-weil-pbc-pushforward-tilde-spec`: in rank one they identify the two source structure sheaves and their ordinary direct images with the associated evaluation modules. Finally `lem-pc-affine-pseudo-coherent-criterion`, whose pseudo-coherent clause matches `perfect.tex` Tag 08E7 (`lemma-pseudo-coherent-affine`), gives precisely pseudo-coherence from those finite-free resolutions. The graph resolution is also consistent with 062F: successively quotienting by y_b-f_b leaves a polynomial ring on the remaining variables, in which the next monic linear polynomial acts injectively. I read 062F's hypothesis and proof and the regular-immersion Koszul discussion in `duality.tex` 0BQZ as a source check, not as uncited extra inputs to the item. No affine equivalence is applied to E and no cohomology of E is asserted quasi-coherent.

For step 3, I read `lem-sfb-closed-pushforward-pseudocoherence` and `perfect.tex` Tag 09VA (`lemma-closed-push-pseudo-coherent`), including its two directions. Its actual statement requires a closed immersion and a pseudo-coherent ordinary pushed-forward structure module, exactly the facts established in steps 1 and 2; it quantifies over every integer m and every derived object without quasi-coherence. It preserves the same m. Its use twice proves two intermediate equivalences; it does not itself assert independence of polynomial embeddings.

For step 4, I read `lem-pc-ringed-spaces-derived-direct-image-composition` and `cohomology.tex` Tag 0D5T (`lemma-derived-pushforward-composition`). They give the isomorphism for unbounded derived categories and arbitrary morphisms of ringed spaces, so both composites identify with Rh_*E, without any boundedness or acyclicity assumption. I reread `def-sfb-m-pseudo-coherent-complex`: composing its local approximation with a derived isomorphism retains all cohomology isomorphisms above m and the surjection in degree m. This explicit argument justifies transport of the condition; it hides no comparison lemma. The final equivalence is then propositional transitivity.

I checked that every proof use has a verbatim excerpt in `citations.json` and that `proof_deps` is exactly the union of uses. I traversed the existing dependencies of all six cited statement nodes: none reaches this item, so these citations create no cycle. The three non-leaf tools from other units (graph resolution, affine criterion, derived composition) are declared with their limited roles in `split_report.tool_uses`; the two structure-module comparisons are already Mathlib leaves. No statement dependency was removed and no inherited metadata was deleted.

Small cases checked: n=0 or r=0 gives a legitimate evaluation on an empty list and the identity graph; n=r=0 reduces both presentations to the same closed immersion. The zero ring/empty scheme and E=0 cause no problem, since the resolution and all cited comparisons allow zero rings or modules. A ring with zero divisors, such as Z/4Z, still has injective multiplication by each monic coordinate difference after the previous quotients, so no domain or regular-base assumption has slipped in. Arbitrarily negative m and E with non-quasi-coherent low-degree cohomology are handled by 09VA at exactly that m. All step texts are below 2000 characters; no long step hides a lemma. No SGA source, compiler, Lake command, repository write or manual git operation was used.

## Unfinished work

None in this one-level split. The cited existing unsplit closed-pushforward lemma remains its own future DAG item; its complete statement is sufficient here. Delivery preflight is run by the authorized server tooling.
