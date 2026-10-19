## Worker report

Files written:

- `dag/nodes/sec-proetale-coefficients/sk-def-pe-morphisms.json`: definition, split; no complete Mathlib match for the bundle.
- `citations.json`: empty list, because this definition has no proof steps.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No existing node other than the item was edited. All writes are confined to this sandbox; the required search command maintains `searches.jsonl` here.

Attachments: none. The blueprint tag has no hit in `WeilConjectures/` or `Comparator/`. The project has `Algebra.IndEtale` (`WeilConjectures/RingTheory/ProEtale/IndEtale.lean:47`), `AlgebraicGeometry.proAffineEtale` (`WeilConjectures/AlgebraicGeometry/Morphisms/ProAffineEtale.lean:164`), its affine ring equivalence at line 328, and `AlgebraicGeometry.WeaklyEtale.etale` (`WeilConjectures/AlgebraicGeometry/Morphisms/WeaklyEtale.lean:46`). These cover parts of the imported text, not every clause including its final nonexistence warning and refinement theorem. I therefore make no whole-item ATTACH claim or assumption about transitive sorry-freeness. Mathlib's `AlgebraicGeometry.WeaklyEtale` is used through its existing definition node.

WANTED: none.

## Sources and existing nodes

I read the current blueprint `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-pe-morphisms/_section.md` in full, its chapter `_section.md`, and the existing `det-pe-morphisms-etale-comparison` statement and proof. The item's base record has neither `chapter` nor `unit`; there is no corresponding chapter/unit JSON record for this new section. I followed its actual current blueprint source and preserved its maintainer-owned metadata rather than inventing a binding.

The mathematical definitions were checked against:

- Stacks Tag 097I, `proetale.tex`, `definition-ind-etale`: a filtered colimit of étale algebras.
- Stacks Tag 094P, `more-morphisms.tex`, `definition-weakly-etale`: both the scheme map and its diagonal are flat.
- Stacks Tag 092B, `more-algebra.tex`, `definition-weakly-etale`: both the ring map and tensor multiplication are flat.

I also read Tag 097N (`proetale.tex`, `lemma-ind-etale-implies`), Tag 094S (`more-morphisms.tex`, `lemma-weakly-etale-characterize`), Tag 094X (`more-morphisms.tex`, `lemma-when-weakly-etale`), and Tag 097Z (`proetale.tex`, `proposition-weakly-etale`) to distinguish properties and a forward refinement theorem from the definitions. No SGA source or route is used.

Whole-DAG keyword searches and `tools/blueprint_refs.py search` for `ind-étale`, `weakly étale`, and `pro-étale affine` found the existing definitions and the blueprint's own comparison statement. I opened the statements of every actual dependency:

- `def-weil-pbc-ind-etale-algebra` defines the filtered presentation with finitely presented étale terms, states the corresponding affine inverse-limit presentation, and gives the ring-level tensor multiplication definition. Those are precisely the facts reused in the first, second and last paragraphs. Its extra ind-Zariski clause is not used.
- `def-weil-pbc-category-colimit` defines small indexing categories, colimits, and filteredness including nonemptiness. It supplies the convention in paragraph 1. In paragraph 3 cofilteredness is explicitly defined by filteredness of the opposite category; the limit universal property is written out, so this colimit node is not misquoted as already stating a theorem about inverse limits.
- `def-weil-affine-spectrum` supplies Spec and its contravariant maps. It is not cited for preservation of limits or colimits. The specific affine ind-étale presentation is already stated in `def-weil-pbc-ind-etale-algebra`.
- `def-weil-etale-morphism` supplies the scheme-level meaning of the étale maps in the general presentation. No theorem on their stability is inferred from that definition.
- `def-weil-weakly-etale-morphism` says exactly that the morphism and diagonal into the fibre product are flat. It supplies the scheme definition, not the affine-chart equivalence or any comparison theorem.

I inspected `lem-weil-pbc-spec-small-colimit-limit` too. Its small-category statement would supply a general Spec/limit theorem, but adding it is unnecessary: the cited existing ind-étale definition already states the precise affine presentation used here. I rejected `def-weil-inverse-system` as a dependency: it defines integer-indexed towers only, whereas this item's indexing category is arbitrary small cofiltered. The new text instead writes out the required universal property.

## Statement organization and removed edges

The source labels this item a definition but mixes definitions, comparison theorems, and motivation. Following stages/1-dag.md §2 (claims inside definitions), the item now records the definitions and cites their actual prerequisites. The four mathematical comparison claims are already stated, with exactly the relevant hypotheses, in the existing blueprint node `det-pe-morphisms-etale-comparison`:

1. Its clause 1 is the source's assertion that every étale morphism is weakly étale.
2. Its clause 2 is the affine-base, ind-étale assertion that every affine pro-étale morphism is weakly étale.
3. Its clause 3 is the converse with the locally-of-finite-presentation hypothesis.
4. Its clause 4 is the affine-chart equivalence with flatness of the ring map and tensor multiplication.

These are not new nodes or replacement proof steps. I did not claim to have split that existing comparison item; its imported proof remains for its own worker. In particular I did not cite its proof as if it were its statement, or use the definition alone as a proof of flatness, étaleness, or Zariski locality.

The last paragraph of the source is explanatory: flatness alone is insufficient, global pro-étale presentations cannot be required, and the appropriate refinement is `sk-thm-pe-indetale-refinement`. The latter statement uses the notions defined here. It is a forward pointer, not a prerequisite for defining them. Removing it from `stmt_deps` repairs the direct circular dependency. Its mathematical content is retained in that existing theorem; this split does not assert a global-presentation equivalence. I did not edit the maintainer-owned `pointers` or `import_flags` fields. This report and `split_report` retain the forward-reference mapping.

The general presentation explicitly uses a small nonempty cofiltered category and absolutely affine stages over X. These spell out the blueprint's pro-étale convention; they do not impose affineness on X, a finite-presentation condition on the limit, or a faithful-flatness condition on its structure morphism. The source's stage affineness is not replaced with relative affineness. No target statement or coefficient category was changed. No mathematical statement was found false, so there is no STATEMENT-DISPUTED claim.

## Mathlib searches

All seven searches in the item were actually run with `msearch.py Q48 sk-def-pe-morphisms`; their tool and query strings are copied from the sandbox log. Both LeanFinder phrasings returned ordinary étale-algebra and étale-morphism results, including `Algebra.Etale.finitePresentation`; neither returned this full bundle. LeanSearch returned ordinary étaleness and `Scheme.isAffine_of_isLimit`, which is only affineness of an already existing limit, not the definition or comparison claims. Loogle returned an unknown-identifier diagnostic for `Algebra.IndEtale, Algebra.WeaklyEtale` and zero hits for the second query `"IndEtale"`. Those are limitations of those queries/indexes, not stand-alone evidence of absence.

The two logged greps found `AlgebraicGeometry.WeaklyEtale` and `Algebra.WeaklyEtale` in Mathlib and the generic ind-morphism API. I read the scheme class at `Mathlib/AlgebraicGeometry/Morphisms/WeaklyEtale.lean:44`, the generic filtered-colimit definition at `Mathlib/CategoryTheory/MorphismProperty/Ind.lean:60`, and the returned project definitions at the paths above. The generic categorical machinery helps implement the definitions but does not, in one declaration or one-line specialization, give the entire original item and its comparison/refinement assertions. I therefore reused the existing Mathlib definition node and recorded no whole-item Mathlib match.

## Not duplicates

No new nodes were created. Existing ind-étale, weakly étale and spectrum definitions were reused, and all comparison clauses already have a blueprint statement node. `blueprint.same_as` is empty because no other blueprint node states the complete combined definition, including the arbitrary-base pro-étale affine convention; the proper-base-change ind-étale definition overlaps substantially but also introduces ind-Zariski and does not give this arbitrary-base convention.

## Review by Q48

I checked B–E with the current source and node statements open. This is a definition-only split, so there are no numbered proof steps and no proof-step quotations to provide; `citations.json` is `[]`. Every definitional citation was checked clause by clause above. In particular the universal-property text is explicit, no integer-tower result is applied to a general category, and no definition node is used for the comparison theorems. Those distinctions repair the imported uncited assertions without creating any elementary, duplicate or clause-restatement node.

For hypotheses, the ind-étale presentation is in commutative R-algebras, not merely rings; the terms are finitely presented and étale. Étale algebras being finitely presented agrees with the inspected Mathlib source and Tag 097I's convention. The affine base is used only in the ring presentation, whereas the general definition allows arbitrary X. The general diagram is small and nonempty cofiltered, all maps are over the same X, and the written universal property is in X-schemes. The diagonal has source U and target U ×_X U. The multiplication is B ⊗_R B → B, not a map involving a different base ring or an arbitrary B-module structure.

I tested the conventions on the identity R → R (a one-term étale presentation), the zero R-algebra (empty spectrum, still allowed), and R → R_f (one-term étale localization). None is inadvertently excluded by a faithful-flatness or nonempty-source assumption. The indexing category is nonempty even when a stage scheme is empty. The general definition also permits a constant diagram at any affine étale X-scheme; it does not replace that by an assertion that X is affine. As a check on the source's warning, k → k[t] is flat but the tensor multiplication k[t_1,t_2] → k[t] has nonzero kernel (t_1 − t_2) and is not flat, so it is not weakly étale. That motivation is not treated as a proved comparison theorem of the definition.

Corrections made: replaced the single circular refinement dependency by the five actual notion dependencies; separated properties already owned by `det-pe-morphisms-etale-comparison`; made the indexing and absolute-affineness conventions explicit; filled the blueprint search result and recorded only executed searches. All original blueprint/import metadata remains unchanged. There are no new node statements needing a separate source or edge-case test, no hidden construction from a sorry, and no off-unit proof tool use.

Unfinished work: none for splitting this definition one level. The independent second reader should check the separation of the source's comparison properties against their already existing statement node before delivery.

## Dry-run tooling

The first required `deliver.py ... --no-push` attempt reached preflight but reported unrelated changes to `coord/blueprint-index.tsv`, `coord/ledger.md`, and `coord/live-dag-tip.txt`. None is in this sandbox and I made no edits to them. This appears to be a base-ref change during temporary-worktree preparation. I reran the authorized delivery tool against its refreshed base, without changing or working around the tool.

## Second reading by Q48

- Item statement: checked the blueprint node `sk-def-pe-morphisms` and Stacks Tags 097I (`definition-ind-etale`), 094P (`definition-weakly-etale` for schemes), 092B (`definition-weakly-etale` for rings), and 097Z (`proposition-weakly-etale`); verdict: the hypotheses and four definitions agree, including the nonempty small cofiltered presentation and the diagonal target $U\times_XU$.
- Proof steps: none; this is a definition-only node, so there are no steps or citations to verify.
- New nodes: none; there are no new-node statements, Mathlib leaves, or new proof dependencies to audit.
- Edge cases: checked the identity algebra, the zero algebra/empty spectrum, a localization, and a constant one-stage affine étale presentation; verdict: no unintended nonemptiness, affineness of $X$, or faithful-flatness hypothesis was introduced.
- Existing dependencies: opened `def-weil-pbc-ind-etale-algebra`, `def-weil-pbc-category-colimit`, `def-weil-affine-spectrum`, `def-weil-etale-morphism`, and `def-weil-weakly-etale-morphism`; verdict: each cited notion is defined there and is used only for its stated meaning. The comparison assertions remain in `det-pe-morphisms-etale-comparison`.
- Mathlib searches: checked the seven recorded `msearch.py` entries and the existing `AlgebraicGeometry.WeaklyEtale` leaf; verdict: searches are present and no whole-bundle declaration matches.

Changes made in this second reading: expanded the item's external source records to name the exact Stacks tags and labels for each definition (097I, 094P, 092B, and 097Z), because the prior record named only the refinement proposition; no mathematical statement or dependency edge was changed.
