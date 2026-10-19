# Worker report

Item: `def-per-rational-surface-singularity`. Group: Q14. Stage 1, direct delivery, 2026-10-19.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/def-per-rational-surface-singularity.json`: existing definition, marked split; its mathematical conditions and dependency list are retained; local/domain/normal-scheme conventions and the cohomology module action are explicit inline, with preserved and supplemented Mathlib search records.
- `citations.json`: empty because a definition has no proof steps.
- `report.md`: this report.

No new nodes and no Mathlib leaves were created. No Lean files were written or compiled.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id, the Stacks tag `0B4N`, and rational-singularity/normal-modification terminology. No sorry-free project declaration states this definition. The upstream master checkout was treated only as reference material.

## WANTED

None. The source and all definition references are present locally.

## What changed and what was wrong

The imported item was an unsplit definition with no proof. I retained the source-faithful hypotheses: a commutative Noetherian normal Nagata local domain of dimension two; proper normal integral modifications of its affine spectrum that induce an isomorphism on function fields; vanishing of first Zariski structure-sheaf cohomology for every such modification; and the existence of a uniform nonnegative integer bound on the module lengths in the reduction-to-rational-singularities condition. The cited notions are the existing DAG definitions listed in `stmt_deps`, so no child node is justified. The Stacks definition at Tag 0B4N uses the equivalent language of a local normal Nagata domain of dimension two and proper birational modifications; the present statement makes the modification objects and the length bound explicit without changing the intended condition.

The inherited blueprint ancestry runs through `lem-per-artin-gabber-affine-curve` and the surface-resolution chain. I preserved that provenance. The current main-20261015 ancestor, its chapter, and its unit were read; no current blueprint node states this auxiliary definition. Searches for `rational singularity`, `bounded modification`, and `0B4N` found no equivalent imported definition. No statement dispute was found.

## Not duplicates

No new nodes were created. The ten cited definition nodes were searched by id, key words and Stacks source tags and reused; none duplicates this combined definition.

## Searches and blueprint

I read `dag/chapters/sec-deligne-laumon-a1.json`, `dag/units/sk-p-dl-a1-perverse.json`, the item node, and Stacks `resolve.tex` around Tag 0B4N and the preceding definition of modification. The earlier Mathlib searches were read from `searches.jsonl` and reused: two LeanFinder phrasings, Loogle and Mathlib grep. This recovery also ran LeanSearch and two Loogle patterns. The first Loogle pattern had an unknown identifier; the valid pattern `AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsProper` returned only a commutativity theorem for proper integral group schemes. The earlier malformed Loogle query is retained and explicitly marked as a query error, rather than evidence of absence. Current repository searches are preserved as inherited records. The returned declarations concern normalization, reduced/integral schemes, smooth loci or no declarations, so there is no Mathlib match.

## Review by Q14

I checked the source statement against Stacks `resolve.tex`, Tag 0B4N (`resolve-definition-reduce-to-rational`) and the opening of the vanishing section, where a modification is recalled as a proper birational morphism between integral schemes. The local-ring hypotheses in the node (Noetherian, normal, Nagata, local domain, Krull dimension two) match the source; the maximal ideal is present, and no residue-field hypothesis was silently added. The node's modification clause requires properness, integrality and normality of the model, together with equality of function fields, which is the explicit form of the source's normal proper birational modification convention. The two cohomological clauses use exactly first Zariski cohomology of the structure sheaf and module length, and quantify over every such modification with one uniform integer bound.

Because this is a definition, there are no proof steps or non-elementary citations to split, and `citations.json` is therefore empty. Each statement dependency was opened and confirmed to provide the notion named in the statement: Noetherian/normal/Nagata/dimension-two ring conditions, affine spectrum, proper morphism, integral scheme, function field, Zariski cohomology, and module length. No dependency is used for a theorem beyond its stated definition. I checked edge cases at the level of the definition: the bound is required to be an integer (b\ge 0), the quantifier includes the identity modification, and the rational-singularity clause requires vanishing for every modification rather than only one resolution. Mathlib searches found no existing declaration of this combined notion. No source error, hidden lemma, duplicate, or attachment was found.

## What remains

The recovered split passed its initial server dry run at `79b083912e`. After the clarifications and search repairs described below, the final dry run and push are performed with the prescribed delivery tool; independent maintainer review follows delivery.

## Recovery review by Q14, 2026-10-19

I retained the previous split, source, citations file, report, and logged searches, compared every item field with the current repository, and ran the initial dry run before editing; it exited successfully. The shared item remains unsplit, so no finished live split is being replaced. There are no project declarations matching the item tag or rational-singularity, bounded-genus, or reduction-to-rational terminology in the read-only `WeilConjectures/` source.

I reread `resolve.tex` at `definition-reduce-to-rational` (Tag 0B4N, verified in `tags/tags`) and the modification convention at `section-vanishing`, lines 1358–1364. Nagata already includes Noetherian in the cited definition, so stating Noetherian explicitly adds no hypothesis. Normal modifications here have integral normal source and are proper birational over Spec R. The function-field node explicitly defines k(X) for any integral scheme, not only for curves, so it applies to these surfaces. The normal-ring dependency gives normal domains but does not itself define a normal scheme: I corrected that omission by spelling out normality of Z as normality of every local ring. I also spelled out locality, the domain convention, and the R-action induced on cohomology by structure-sheaf multiplication. These are definitional clarifications of the same conditions, not a change in quantifiers or hypotheses.

For B1–B10 I checked that no new statement or duplicate node is being introduced, the statement is self-contained, every nonbasic notion has an existing definition citation or an inline definition, TeX is decoded once, the tag and label match, and the unsuccessful query syntax is recorded honestly. For C1–C8 and D1–D5, this is a definition with no proof steps, so it needs no theorem citation, hidden-lemma extraction, tool-lemma exception, or step quote; `citations.json` remains `[]`. All ten statement dependencies were opened and their statements read. In particular, properness is exactly the proper-morphism definition; integrality is supplied by def-pc-integral-scheme; def-sc-function-field covers general integral schemes; def-sc-zariski-cohomology gives ordinary Zariski derived global sections; and the module-length node explicitly permits infinite length, so the finite integer bound excludes it.

For E1–E7 I checked the uniform quantifier over every modification, that the same bound b works for every Z, that b may be zero, and that the identity modification belongs to the quantified class. No assumption that a resolution exists is used. Rings of dimension zero or one are outside the stated domain of this definition, rather than asserted to satisfy a surface theorem. There are no long proof steps, assertions about base change, or source errors to hide. No SGA source or compiler was used.
