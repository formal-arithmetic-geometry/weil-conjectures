# Stage-1 report: def-sfb-m-pseudo-coherent-complex

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-m-pseudo-coherent-complex.json`: definition; marked split after auditing the three existing statement dependencies; no Mathlib match. The mathematical statement, source, dependency lists and inherited searches are retained. Five actual Q110 search records are appended.
- `citations.json`: empty list, because the item is a definition with no proof steps or proof citations.
- `searches.jsonl`: actual command-generated search log. No new nodes and no new Mathlib leaves.

## Attachments

None. The item tag has no hit under `lean/WeilConjectures/`. I read `AlgebraicGeometry.Scheme.IsPseudoCoherent` in `AlgebraicGeometry/PseudoCoherentComplex.lean:35`: it requires bounded-above finite-free local representatives and defines pseudo-coherence in all degrees, not the fixed-degree condition here. I read `DerivedCategory.IsMPseudoCoherent` in `RingTheory/MPseudoCoherent.lean:31`: it applies to modules over a commutative ring, not module sheaves on an arbitrary scheme. Neither states this item exactly.

## WANTED

None. All required sources are present locally.

## Problems found and changes

No false or ill-typed statement was found. This is a definition, so stage 1 consists of naming and verifying the notions used, as stages/1-dag.md section 3(2) prescribes. It has no assertion to prove and no reason to invent subsidiary lemmas. I preserved the statement verbatim, `proof: []`, `proof_deps: []`, and `proof_origin: null`.

The inherited blueprint ancestry already ends at null. `python3 tools/blueprint_refs.py ancestor def-sfb-m-pseudo-coherent-complex` confirms None; I did not invent an imported ancestor. Its inherited place identifies the stability/direct-image route and its via chain identifies the relative pseudo-coherence parent. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md` and `sk-thm-sf-ctf-stability/_section.md`, together with the chapter and unit JSON records. No chapter or unit change is needed for this supporting definition.

## Not duplicates

No new nodes were created. The existing item is distinguished from nearby nodes as follows.

- def-sfb-m-pseudo-coherent-complex vs def-pur-pseudo-coherent-complex: fixed integer m versus pseudo-coherence in every degree.
- def-sfb-m-pseudo-coherent-complex vs def-pc-ring-m-pseudo-coherent: sheaves on arbitrary schemes with local strictly perfect witnesses versus modules over a ring.
- def-sfb-m-pseudo-coherent-complex vs def-sfb-relative-pseudo-coherent-complex: the absolute condition on a scheme versus the relative condition on ambient affine-space pushforwards; the relative node needs this definition.
- def-sfb-m-pseudo-coherent-complex vs lem-sfb-ringed-site-m-pseudocoherent-triangle and lem-sfb-ringed-site-pseudocoherent-top-finite-type: those are theorem nodes that spell out the condition inline, not standalone definitions to replace this node.

The DAG searches included Tags 08CB and 08CC and the words m-pseudo-coherent and strictly perfect. I read the relevant nearby statements rather than treating matching tags as identical results. `blueprint_refs.py search pseudo-coherent` returned no blueprint nodes, and `search pseudo` returned only the unrelated filtered-two-colimit definition; the direct search in `literature/blueprint/latest/blueprint/` found no fixed-degree definition. `blueprint.same_as` remains empty.

## Mathlib search review

All five appended records come from the prescribed msearch.py command for Q110 and this item, and their exact tool/query strings are in searches.jsonl. Loogle for PseudoCoherent and grep for pseudo-coherence/strictly-perfect/IsMPseudoCoherent had zero hits. LeanSearch and the first LeanFinder query returned derived-category truncation, localization, and factorization facts. The second LeanFinder phrasing used the equivalent cone-vanishing approximation description and returned cohomological bounds and K-projective/K-injective predicates. I read the returned signatures: none combines local strictly perfect witnesses with the above-m isomorphism and degree-m epimorphism. These are actual no-match results, not unavailable services. The five inherited Q147 records are retained as earlier research, not represented as new Q110 calls.

## Unfinished work

None for the one-level stage-1 task. No Lean was written and no compiler, Lake, or build command was run. The server dry run and direct push are the final validation/delivery actions.

## Review by Q110

I read Stacks `cohomology.tex`, Tag 08CB (`definition-pseudo-coherent`), clauses (1) and (3), Tag 08CC (`lemma-pseudo-coherent-independent-representative`), clause (1) and its proof, and Tag 08C4 (`definition-strictly-perfect`). Tag 08CB defines the condition using chain maps into a representative; such maps give the derived morphisms used here. Conversely 08CC(1) gives precisely the derived-morphism formulation used by this definition. Its proof refines the open covering to represent each derived morphism by a chain map. The item merely chooses that established equivalent formulation as its predicate; it does not assert representative independence as an additional theorem needing a proof dependency.

I opened each of the three statement dependencies. `def-pc-scheme` introduces schemes and open subschemes. `def-pc-derived-category` explicitly supplies the derived category of all structure-module sheaves, so I did not substitute the quasi-coherent subcategory. `def-pc-perfect-complex` explicitly defines strictly perfect to mean finitely many nonzero terms, each a direct summand of a finite free structure module; this is the clause needed here, rather than just its separate definition of perfect objects. Its wording agrees with 08C4. I also read the corresponding existing Lean definitions of the derived category and strict perfectness as a check on the carrier. Restriction to an open and the cohomology-sheaf functors are the operations of those cited categories. Surjectivity means an epimorphism of sheaves, without a demand for surjectivity on all open-section groups.

There are no proof steps, so the C1/C4 proof-citation audit is vacuous and citations.json is exactly empty. In particular I did not cite a definition for a theorem, insert an unproved comparison, create a new node restating a clause, or hide an argument in a long proof step. All data in the definition is quantified witness data, not a chosen object from an unproved existence assertion. B1--B10 are satisfied by the existing self-contained TeX statement, verified tag/label references, recorded searches, and the explicit no-attachment check; no new-node conditions are being evaded.

For the E-section hypothesis and small-case checks, only a scheme and an integer m are assumed. On the empty scheme the empty covering makes the predicate vacuous, correctly. The zero object has the zero strictly perfect witness for every m. A strictly perfect object has its identity witness, whose degree-m map is surjective. On a point with a module concentrated in degree m, the boundary condition asks only for a finite free/projective source surjecting on that module, not an isomorphism; thus it has the correct endpoint. There is no quasi-compactness, Noetherian, coherence, finite-type, or global boundedness hypothesis added: in particular on a non-quasi-compact scheme the local upper bounds need not be uniform. The cover and witnesses are quantified after m, so they may depend on m. These checks found no statement dispute to repair. My changes are limited to recording this completed audit and the actual additional searches.
