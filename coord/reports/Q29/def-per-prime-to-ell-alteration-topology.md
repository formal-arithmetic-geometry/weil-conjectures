# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/def-per-prime-to-ell-alteration-topology.json`: definition, split; no Mathlib match. All ten notions it uses have existing DAG definition nodes. No new nodes or Mathlib leaves.
- `citations.json`: `[]`, since the item is a definition with no proof steps.
- `report.md`: this report.

## Attachments

None. Searched the entire `WeilConjectures/` tree of `/home/ubuntu/weil-src-slopmaster2` for the item tag and alteration, maximally finite, and decomposed terminology; there are no matching declarations. The same search in the read-only upstream master checkout also returned no match. Both recorded Lean audits are `none`; no sorry declaration is being treated as a proof.

## Literature wanted

None. The complete source is present: `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Exposé II, printed pp. 23–28. I extracted it into the sandbox's `ilo.txt` and read the relevant definitions. No SGA route is used.

## Findings and corrections

The retained sandbox had the completed definition node and seven logged Mathlib searches, but no report. Its statement, dependencies, source, ancestry and creation metadata agree with the current repository. The repository item is still unsplit; no current reviewed split or finished declaration supersedes this work. The mathematical statement is unchanged.

Two `grep` records in the retained node did not transcribe the logged query exactly: the first expanded `[Mm]aximally` to `[Mm]aximally[Dd]ominant`, and both appended the search directory to the query. Restored the actual query strings from `searches.jsonl`; their directory restrictions are those logged in `sub` (`Mathlib/` and `Mathlib/AlgebraicGeometry`). Also marked the first Loogle query unavailable because it rejected an unqualified identifier; it is not evidence of absence. The second, fully qualified Loogle query succeeded. All logged results were read, retained and not repeated.

The two LeanFinder phrasings return finite-type, finite, quasi-finite and étale declarations; LeanSearch returns ordinary Zariski and étale topology constructions; qualified Loogle returns Zariski topology and comparisons. None states the alteration category or its generators. Both logged source greps returned zero hits. These generic site and morphism definitions are already represented by the existing dependencies, rather than grounds for declaring this whole item a Mathlib leaf.

The blueprint searches `alteration` and `decomposed` each found zero blueprint nodes. A whole-DAG terminology search and a current-blueprint text search located this definition and its users (uniformization standard form, Gabber regular cover, and standard refinement), not another definition of the same site. The ancestor command confirms `lem-per-artin-gabber-affine-curve`; the retained `blueprint.from.place` and `via` identify the ILO finiteness input in its Verdier-duality step. This is a definition dependency below the unit route, with no replacement proof route and no unit realization fields to change.

## Unfinished work

None for this one-level split. This definition needs no child nodes; it does not assert the uniformization or refinement theorems that its users still have to establish. The dry run and delivery are recorded by the delivery tool.

## Not duplicates

No new nodes were created. The existing alteration theorems use this category and topology; their conclusions do not define it.

## Review by Q29

I read ILO Exposé II §§1.1.1–1.1.2 for maximal points and maximal dominance, Definition 1.1.8 for maximal prime-to-ell finiteness, Definition 1.2.2 for `alt/S`, §§2.1.1–2.1.2 for decomposed étale coverings, and §2.3.1 for the alteration topology. The finite-type, reduced source and generic residue-field finiteness conditions in the first paragraph are precisely Definition 1.2.2 expanded through §§1.1.8–1.1.9; the structure morphism need not be surjective or proper. The second paragraph distinguishes the generic-point condition on a proper generator from the all-points lifting condition on an étale family, exactly as §2.3.1 emphasizes. Complete decomposition means an actual isomorphism on the lifted residue field. The third paragraph uses the generated Grothendieck topology: it does not incorrectly say that the two displayed kinds of families alone form a pretopology. Covering families and refinement are defined explicitly and make no refinement theorem implicit in the statement.

I opened the statements of all ten dependencies. `def-pc-scheme` defines schemes, their morphisms and affine schemes; `def-weil-pbc-noetherian-ring` defines Noetherian rings, so the finite affine-cover condition defines Noetherian schemes inline. `def-weil-finite-type-morphism` gives finite type, `def-pc-reduced-scheme` gives reduced schemes, `def-weil-irreducible-components` gives irreducible components, and `def-weil-residue-field` gives both residue fields and their induced maps. Thus the generic-point and extension-degree conditions have the asserted objects. `def-weil-etale-morphism` supplies étale morphisms, `def-weil-proper-morphism` supplies proper morphisms, and `def-weil-surjective-morphism` supplies surjectivity. `def-weil-pbc-topos` explicitly defines sieves and the three Grothendieck-topology axioms, so it is a valid dependency for the topology, not merely a topos definition with a misleading title. These statements say everything taken from them; none is being cited for an additional theorem about its notion.

There are no proof steps and hence no non-elementary proof facts to audit under C1/C3/C4, no long steps hiding lemmas, and no proof citations to quote. Empty `proof`, `proof_deps` and `citations.json` are intentional for a definition. I checked B1–B10: there are no new statement-only nodes, no unmatched notions, no fabricated source tags, no duplicate or unjustified Mathlib leaves, and no attachment to a partial or sorried declaration. I checked D1–D5: no clause has been relabelled as a new node, and no proof obligation has been moved out of sight. For E1–E7, the Noetherian and prime hypotheses are explicit, maximal prime-to-ell finiteness quantifies over generic points in the target image, and étale decomposition quantifies over every target point. No excellence, regularity or invertibility hypothesis is silently imposed on this definition.

As small cases, the empty reduced scheme is an object and has vacuous generic conditions; it cannot give a surjective generator over a nonempty target. Identity maps on reduced objects have degree one and satisfy both generator conditions when applicable. For `S = Spec(k)`, a finite field extension of degree divisible by ell is a legitimate object of `alt/S` but its singleton map to `Spec(k)` fails the maximal prime-to-ell condition; a finite extension of prime-to-ell degree satisfies it. A disjoint union can qualify when one generic lift over each target generic point has prime-to-ell degree, even if other lifts have ell-divisible degree: the source condition is existential in that clause, as the retained statement says. Over a nonreduced base, sources remain reduced, rather than treating the base itself as an object. No mathematical correction was needed; the search-log transcription and failed-query verdict were corrected as described above.
