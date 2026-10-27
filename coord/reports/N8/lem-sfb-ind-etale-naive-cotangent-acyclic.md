## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ind-etale-naive-cotangent-acyclic.json: item, statement, split in four steps; not a Mathlib leaf. The statement and statement dependencies are unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-filtered-colimit-naive-cotangent-comparison.json: new statement-only node, unsplit, no Mathlib match. Its conclusion is the canonical quasi-isomorphism, hence an isomorphism in the derived category, for arbitrary small filtered diagrams of algebras over a fixed ring.
- citations.json: nine entries, one for each use in each numbered step, with verbatim text from the cited statement.

## Attachments

None. Searched lean/WeilConjectures by the item tag and by ind-etale, naive cotangent, IndEtale, cotangent/colimit and 07BQ. The ind-etale definition and finite-subfield cotangent reduction exist, but neither states the item or the new comparison. The finite-subfield theorem does not cover general algebra diagrams or degree-zero cohomology. No attachment is claimed for a sorried declaration.

## WANTED

None. All sources used are present locally.

## Corrections and provenance

The imported item was an unsplit statement, with no proof and no lean_audit record. Its prior Mathlib searches are retained. The statement is correct and needs no STATEMENT-DISPUTED correction. The standard complex is in degrees -1,0; the definition node uses the corresponding homological degrees 1,0. This is a change of indexing, not a change of object.

I read the current blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md and the chapter/unit records. This is the inherited supporting local algebra chain for the direct-image argument, through the strict-henselization comparison. I did not change the chapter or unit route. The ancestor command reports blueprint.from.node = None for the existing created.item chain; the new node retains that result, the full via chain, and the precise inherited proof place. Searches of the whole blueprint for cotangent, naive cotangent and 07BQ found no existing blueprint version of this comparison. A broader colimit search did not identify a cotangent comparison either.

The conormal criterion and presentation-comparison theorem are generic algebra tools from other units. They are declared in split_report.tool_uses: they supply finite-presentation etale acyclicity and its comparison with the canonical, possibly infinitely generated presentation. They do not replace a step of the unit's route.

## Not duplicates

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-sfb-locally-dense-cotangent-h1: that node concerns a locally dense subpresheaf on a site and sheafified first homology; the new node concerns a small filtered algebra diagram and the whole two-term derived object over a fixed base ring.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-sfb-strict-henselization-naive-cotangent: that node compares strict henselizations across a local ring map, including tensoring and change of base; the new node is the general fixed-base colimit comparison used to prove their relative acyclicity.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-sfb-ind-etale-naive-cotangent-acyclic: the item assumes ind-etaleness and proves vanishing; the new node has no etale hypothesis and identifies complexes for arbitrary filtered algebra diagrams, which may have nonzero cotangent cohomology. The item still proves stagewise vanishing and compatible inverse differentials.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-sfb-directed-union-cotangent-h1: the existing node requires inclusions of subalgebras and proves representative descent and eventual-zero detection only for first homology. The new node allows arbitrary transition maps and states the canonical derived comparison for both terms.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-sfb-sheaf-polynomial-cotangent-comparison: that node compares polynomial presentations of sheaf algebras after sheafification on a site, rather than a filtered diagram of ordinary algebras.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-weil-pbc-transitivity-gamma: that node is a Jacobi-Zariski exact sequence for three fields and specifies its connecting map, rather than a cotangent colimit comparison.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-weil-pbc-h1-cotangent-finite-subfields: that node deduces first-homology vanishing for a field from its finitely generated subfields; it neither treats arbitrary algebra diagrams nor identifies their two-term complexes.

lem-sfb-filtered-colimit-naive-cotangent-comparison vs lem-weil-pbc-field-char-p-h1-cotangent-vanishing: that node is vanishing for fields over their prime field in positive characteristic, not a general colimit comparison.

## Review by N8

For the item I read Stacks algebra.tex, Tag 07BQ (lemma-colimits-NL), including its proof in canonical polynomial presentations, and Tag 00U1 (definition-etale), together with more-algebra.tex, lemma-henselization-NL, first proof paragraph. That paragraph explicitly obtains relative acyclicity from filtered etale presentations using those two algebra facts. For the new node I read the same 07BQ statement and proof, including both the conormal and free differential terms. Its stated small-filtered-category form is the finite-data generalization of the source's directed-set form: finite collections of representatives and equalities can be moved to a common receiving object and parallel arrows equalized. It is deliberately left statement-only for its next worker. The canonical comparison is specified as a chain map and in the derived category, not just as a list of unrelated per-degree isomorphisms.

Step 1 uses the actual statements of def-weil-pbc-ind-etale-algebra, def-weil-pbc-finitely-presented-algebra and lem-weil-pbc-etale-ring-map-conormal-criterion. I checked that the first supplies a filtered presentation by finitely presented etale algebras, the second supplies finitely many polynomial variables and a finitely generated kernel, and the third gives bijectivity of exactly the displayed conormal differential. The etale hypothesis is the induced affine morphism's etaleness, as used in the definition and the existing conormal criterion. I do not apply that finite-presentation criterion directly to the colimit algebra.

Step 2 uses the statements of lem-weil-pbc-polynomial-ring-kahler-basis-any-variables and lem-weil-pbc-nl-presentations-homotopy-equivalent. I checked the polynomial basis formula, including its tensor-base-change consequence, so the formal-partial-derivative maps agree with the maps into tensor differentials. The homotopy statement permits arbitrary variable sets on both sides, including the canonical presentation. I checked the contracting-map formula s = phi_1 d^{-1} psi_0 + h' against both chain equations and both primed homotopy equations in its statement: multiplying gives s delta = 1 and delta s = 1. Thus no unrecorded assertion that the finite and canonical presentation terms themselves are isomorphic is used.

Step 3 uses the new comparison node's explicitly specified canonical diagram and degreewise colimit, and def-weil-pbc-category-colimit for the unique induced map out of each colimit. I checked the inverse-naturality equation u delta_j^{-1} = delta_k^{-1} v by multiplying the chain-map equation on both sides. The two inverse identities follow by precomposing with every coprojection and applying uniqueness. This is an elementary categorical argument; it does not smuggle in exactness of filtered colimits or flatness of the colimit algebra. The existence of the degreewise module colimit is part of the new comparison statement's construction, for a small index category.

Step 4 uses the quasi-isomorphism asserted by the new comparison and the precise quasi-isomorphism/localization definition in def-weil-abstract-derived-category. It first obtains zero kernels and cokernels as underlying R-modules and then as S-modules, which is valid since restriction of scalars changes neither elements nor the zero submodule. The inverse of the S-linear differential is checked to be S-linear explicitly. The final map to zero is a quasi-isomorphism of S-module complexes and therefore becomes invertible in D(Mod(S)). This avoids a hidden comparison between derived restriction of scalars and derived scalar extension.

I checked sections B-E of delivery-errors.md against these files: the new node introduces its own objects and all nonstandard notions have definition citations; it has no proof or proof dependencies; all searches recorded for it were actually run with msearch.py, including a second semantic phrasing, and their outputs were read. Searches hit general module/ring colimit constructions and cotangent functoriality, not this comparison. General existence of colimits does not prove compatibility with the canonical polynomial-kernel quotient. The original item's searches also point only to formal-etale vanishing, not a filtered-colimit theorem. I checked the cited statements themselves, not their internal proofs; citations.json quotes their actual text. The only new lemma is the genuinely general comparison, not a restatement of etale vanishing or a two-line step of the assembly. The non-elementary steps have 580, 876 and 720 characters; none exceeds 2000 characters.

Small-case checks: the identity algebra R has an acyclic canonical presentation complex even though its terms need not be zero; the finite presentation with no variables has zero differential terms and the homotopy formula applies. For the zero algebra all modules are zero and the differential is the unique isomorphism. A one-object identity diagram makes the new comparison the identity. A filtered diagram eventually constant at a quotient, e.g. k[e]/(e^2) -> k, tests noninjective/nonflat transitions in the new general lemma; it makes no etale claim for that quotient map. An etale system k x k -> k via a projection tests noninjective transitions in the item. No index category is empty, and no Noetherian or locality assumption is used. There is no new hidden lemma in a long step.

## Unfinished work

None for this one-level split. The new comparison node is intentionally unsplit, as the stage-1 contract requires for new dependencies. Full independent mathematical review remains with the maintainer.
