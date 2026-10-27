## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fibred-cover-detects-exactness.json`: statement, split using existing DAG nodes; Mathlib searches found no match for the whole fibred-site statement.
- `citations.json`: a verbatim statement quote for every proof-step citation.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. Three existing Mathlib leaves are reused.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, fibred/fibered categories, and exactness detection/restriction notions. No declaration states this item. The unrelated equifibered natural transformation and RelativeProj documentation hits are not attachments.

## WANTED

None. The needed sources are present locally.

## Corrections and scope

The mathematical statement is unchanged. Added the existing exact-sequence and etale-morphism definitions to statement dependencies because the statement uses both notions. The imported pushforward convention is irrelevant to this particular proof, but remains in the statement without alteration. The old source-place phrase about an augmented complex belongs to the parent application; the proof here establishes precisely middle exactness and its zero-endpoint cases.

The inherited blueprint ancestry has `from.node: null`, with a detailed place and a long via chain. `blueprint_refs.py ancestor` likewise printed None. I preserved the inherited ancestry instead of inventing a blueprint id. Read the latest unit and detailed direct-image proof: this is a supporting local exactness input below direct-image step (3), not a replacement of the unit's route. Whole-blueprint searches for exactness, covering fibred, and locally surjective yielded no equivalent blueprint statement. A general-site local lifting criterion already follows immediately from three existing nodes, so no new criterion or clause-restatement node was created.

## Unfinished work

None in the one-level split. No Lean was written or compiled; no repository or launcher file was changed.

## Not duplicates

No new nodes were created. Existing kernels, kernel-lift exactness and local-surjectivity results were reused rather than duplicated.

## Review by Q120

I read Stacks `stacks-sheaves.tex`, Tag 06XD, label `lemma-check-exactness-covering`, its full statement and proof. Its hypotheses are exactly the local essential-image covering hypothesis and exactness after precomposition, for any of the listed topologies; the present item is its etale case. I also read `sites-modules.tex`, Tag 03CN, label `lemma-abelian-abelian`, including (2), (5), (6) and their proof. This supplies the sectionwise-kernel and local-section interpretation used to make 06XD explicit. I checked the covering axioms in `sites.tex` and exactness in `homology.tex`, Definition 010E. There are no new-node sources to review.

For step 1 I opened the statements of `lem-weil-pbc-sheafification-exact`, `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift` and `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`. The first explicitly says kernels are sectionwise; the second says exactness is equivalent to epimorphic factorization into a kernel; the third gives local lifts for every object and section on an arbitrary site. Thus none is being cited for a result only in its proof, or specialized from a topological-space theorem. Both fibred etale sites fit the fixed small-skeleton convention. The factorization exists because ba=0.

Step 2 is elementary: the supplied object isomorphism gives an invertible restriction map, and naturality of b proves that the transported section is still in its kernel. It uses the local-image hypothesis directly, without requiring any morphism in X to lift to U.

In step 3 the same three general statements give local preimages on U. I read `def-sfb-stable-pointed-moduli-groupoids`: its explicit sentence that morphisms of fibred categories are functors over schemes is the precise fact needed here. Hence the image of a covering family has the identical underlying jointly surjective etale family. This argument needs no full/faithful or representable functor. I read `def-weil-pbc-sites-and-cohomology`: its singleton-isomorphism and covering-composition axioms justify adjoining the chosen isomorphism and composing the two covering families. The displayed equation is rewritten by contravariant functoriality, not by an unstated comparison theorem.

Step 4 uses the local-epi and kernel-lift statements again to conclude exactness. For F=0, local preimages are necessarily zero; for H=0, every G-section is tested, so this proves the asserted endpoint cases as well. The empty fibred category causes no counterexample: the hypothesis permits it only when all target objects have empty covers, and the same local criterion applies. The identity functor gives the immediate tautological case; automorphisms and nonfaithful functors do not affect any step. I also checked that no pointwise-surjectivity assertion for sheaf epimorphisms was smuggled in: all preimages are produced only after a covering.

Against delivery-errors B--E: no new statement-only nodes, duplicated clauses, unlogged searches, or unintroduced new objects; every non-elementary input is an existing cited statement, with a verbatim quote in citations.json. Each proof step is below 2000 characters. The actual cover-refinement argument is retained in the item, and nothing is moved into a restatement leaf. No statement dispute or source mathematical error was found.
