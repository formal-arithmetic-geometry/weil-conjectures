# Q94: lem-sfb-ringed-sections-forget-abelian

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-sections-forget-abelian.json`: statement, now split in four steps; no Mathlib match.
- `citations.json`: verbatim statement quotations for every step/node pair.
- `searches.jsonl`: actual msearch records. The item's earlier searches have been retained and supplemented by Q94's searches.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The sandbox initially contained only dispatcher markers, with no earlier node or report to recover. The repository was read only; no Lean was written and no compiler, Lake, or git command was run there.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, modulesAbelian/modules_abelian, forgetting/cohomology, and the ringed/unbounded notions found no declaration covering this item. In particular `EtaleModuleCohomologyForget.lean` is a bounded/ordinary, constant-coefficient, scheme-etale comparison, not an arbitrary-ringed-site unbounded statement. These narrower declarations are not attachments.

## Wanted sources

None.

## Corrections and route

The item was an unsplit statement with a correct Stacks source, not a false statement. I retained its statement, hypotheses, initial dependencies, provenance, blueprint fields, and earlier searches. No repair note exists for this id. No statement dispute was needed.

Stacks 0D6J (`sites-cohomology.tex`, `lemma-modules-abelian-unbounded`, lines 4453–4547) constructs the exact displayed comparison from I to J. Its flat-roof proof is not repeated here: the existing, independently reviewed `lem-coef-derived-sections-scalar-coherence` proves the more general arbitrary-scalar comparison, with precisely this representative normalization. It follows Stacks 0D6E (`lemma-derived-pushforward-composition`, lines 4011–4030), which I read. Specializing this existing theorem, rather than introducing a new lemma restating the present item, gives a shorter proof below the unit's argument. The unit's stability route and the inherited norm-coefficient unit-test application remain the same.

The inherited blueprint.from.node is null; `tools/blueprint_refs.py ancestor lem-sfb-ringed-sections-forget-abelian` also returns None. I retained this legitimate inherited absence, specified the inherited paragraph/step in split_report.blueprint, and searched blueprint references for underlying abelian, ringed-sections, and modules-abelian-unbounded. No imported blueprint statement gives the exact item. The derived-sections scalar-coherence lemma is a reusable tool, not a new node or an alternative stability theorem.

## Not duplicates

No new nodes. The existing `lem-coef-derived-sections-scalar-coherence` covers arbitrary ring-sheaf maps and global sections, with derived-unit normalization and composition coherence. The item additionally fixes evaluation at every object and actual site-arrow restriction naturality. I reuse that existing theorem on each slice. Existing bounded scheme-etale comparisons, and unbounded scheme-etale direct-image comparisons citing 0D6J(3), have narrower hypotheses or different conclusions. The existing `lem-sfb-unbounded-sections-localization` already supplies evaluation versus slice sections, so no second localization node was created.

## Unfinished work

None in this stage-1 split. The ordinary existing downstream DAG obligations are not being claimed as proved in Lean.

## Review by Q94

I read delivery-errors B–E in both copies and checked the item with its Stacks sources and the actual statements of all cited nodes open. No new statement-only nodes or Mathlib leaves were created, so B1, B2, B5, B6 and B8 cannot introduce an unsearched or wrongly sourced new dependency. The unchanged statement introduces the small site, ring sheaf, derived categories and all representative complexes; all notions retain their definition dependencies. The proof contains real specializations and commuting-square arguments rather than new nodes restating its clauses (D1/D2). All four steps are below 2000 characters. Sources are identified by their Stacks labels and tags, and the alternate specialization is honestly marked agent-written.

Step 1 uses the definitions of localized sites, constant sheaves, module sheaves and scalar restriction. The localized-site statement explicitly describes objects, coverings, sectionwise restriction and relocalization. The module-category statement explicitly describes sectionwise kernels and sheafified cokernels. Thus the proof of exact restriction uses the same covering families; it does not assume that evaluation on an arbitrary object is exact. Integer-sheaf modules are identified with abelian sheaves by the unique integer action and its local gluing; this is an elementary identification, not an assumption that B is flat over the integers. Every additive map is linear for that action. The exact identification carries complexes and their homotopies unchanged, so also K-injectivity.

Step 2 uses `prop-pur-kinjective-resolutions-exist`, whose statement gives resolutions of every complex for any small commutative ringed site, and `lem-pur-kinjective-restrict-localized`, whose statement explicitly says restriction of a K-injective complex to C/U is K-injective. I read Stacks 08FI (`lemma-restrict-K-injective-to-open`, lines 4314–4325), not merely a definition of K-injectivity. These hypotheses hold separately for B and the integer sheaf, and the slice remains small. Exact restriction from step 1 makes a|U a quasi-isomorphism. I do not assume the underlying abelian complex of I to be K-injective.

Step 3 uses `lem-coef-derived-sections-scalar-coherence`: its statement explicitly permits any sheaf-ring map R to S, requires no flatness, asserts an isomorphism of unbounded derived functors, and says that Gamma(j) is a quasi-isomorphism representing that comparison for an S-K-injective L and an R-K-injective replacement j. Substituting C/U, the integer sheaf, B|U, I|U and a|U satisfies every hypothesis by steps 1–2. The statement also supplies canonical resolution identifications and naturality. `lem-sfb-unbounded-sections-localization` says the comparison to slice sections is an isomorphism in D(Ab), and explicitly states the degreewise identity I(U)=(I|U)(id_U). I read its Stacks source 0D6F (`lemma-unbounded-cohomology-of-open`, immediately after 08FI). Applying it on both sides gives exactly Gamma(U,a), not an arbitrary isomorphism with the same endpoints. Every claimed non-elementary fact is one of these cited statements (C1/C4).

Step 4 uses naturality in the derived module argument from the scalar-comparison statement and naturality of the localization statement. For site arrows, I wrote the explicit degreewise equation J(v) a_U = a_V I_ab(v). The localized-site definition explicitly identifies relocalization with sectionwise identity, so that equation is the actual restriction square, not an unspecified transported square. Localization preserves this equality; step 3's canonical identifications remove any dependence on the chosen replacements.

I checked the edge cases K=0, B the zero ring, B the integer sheaf, a terminal U, an object with empty covering, and complexes unbounded in both directions. The argument uses no finite cohomological dimension, boundedness, torsion, points, or flatness. For B=Z the comparison is the identity by the scalar theorem's identity clause; on a singleton site it is the usual equality of the underlying complex with its derived sections. An empty site has no U, so the quantified assertion is vacuous. No false preservation of K-injectivity by coefficient forgetting occurs (E1–E4).

I declared the four existing general statement tools in split_report.tool_uses, since their units differ from the item's inherited unit. They are tools for its derived-section test; none replaces a stability step or changes the chapter route. No SGA source is used. All step quotations in citations.json are exact full statements read from the repository, preventing quotation drift; proof_deps is exactly the union of uses. The recorded Mathlib services returned only underived forgetting/sections APIs and ordinary abelian Ext cohomology. I read SheafOfModules.toSheaf/sectionsFunctor and Sheaf.H in their Mathlib source, and ran a second semantic phrasing. They do not give an unbounded scalar-forgetting comparison.
