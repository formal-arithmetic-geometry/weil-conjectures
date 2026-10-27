# Q60 — lem-per-surjective-flat-global-dimension

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-surjective-flat-global-dimension.json`: statement; split into four proof steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: twelve step/node entries, each quoting a verbatim part of the cited node's statement.
- `searches.jsonl`: five searches actually run through the authorized msearch command; their results were read. Inherited Mathlib searches in the live item were retained, and the Q60 searches appended.
- `report.md`: this report and self-review.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, flat/surjective/dimension phrases, and the relevant dimension modules. No project declaration states this global scheme dimension formula. The existing `Scheme.dim_eq_topologicalKrullDim` is only the supremum interface and is reused through its node, not claimed as an attachment for the whole item.

## WANTED

None. All sources used are present locally.

## Findings and corrections

The live item was unsplit, with no proof. There was no previous sandbox node or report to preserve and no running delivery. No released repair note exists. The statement is correct and was kept verbatim, together with its statement dependencies and maintainer fields. The chapter, unit, current blueprint proof and parent split were read. This is the global-dimension subargument in Stacks 0AFE used by the existing local-dimension branch of smooth pullback support growth; the unit route is unchanged.

The significant detail suppressed by 0AFE's phrase 'Taking the supremum' is that a constant local topological fibre dimension is not the dimension of every fibre stalk. For example, the generic stalk of the affine line over a field has dimension zero, although the local topological dimension is one. Step 3 instead computes the global dimension of each nonempty fibre and uses its stalk supremum to obtain the required bound and an attaining stalk. No new lemma is necessary: the two existing supremum statements imply both assertions by finite-integer order reasoning.

The searches found flatness interfaces, smooth relative dimension, going down, polynomial-ring dimension and surjective ring dimension inequalities. Those are not the scheme global dimension formula. The useful ring height theorem already has `lem-weil-pbc-flat-height-formula`, a Mathlib leaf; creating a second node for it would duplicate the DAG. Five Q60 searches are recorded exactly as run, including the second semantic phrasing, with no unavailable service misreported as no match.

## Unfinished work

None in the split. Required delivery validation and push are performed after this report is written.

## Not duplicates

No new nodes were created. Existing nodes for 00ON, 0HA1, 04MU and 0B7I are reused. Whole-DAG searches by tags and statements and blueprint_refs searches for dimension, surjective flat, relative dimension, dimension formula, 04MU and 00ON found no independent blueprint statement duplicating this item. In particular, the parent local formula depends on this item, so citing that parent would be circular; the proof does not do so.

## Review by Q60

I read Stacks `morphisms.tex`, Tag 0AFE, both proof paragraphs, especially its invocation of Algebra 00ON and Properties 04MU. I also read the actual statements and relevant text of Algebra 00ON (`lemma-dimension-base-fibre-equals-total`), 00FN (`lemma-Noetherian-permanence`), Schemes 01HV (`lemma-spec-sheaves`), 0HA1 (`lemma-local-ring-fibre`), and Topology 0B7I (`lemma-dimension-supremum-local-dimensions`). The item has precisely the flat, locally Noetherian hypotheses required by 00ON and the nonempty surjective setting reached in the first paragraph of 0AFE. There are no new nodes whose source needs separate verification.

For step 1 I opened the three cited node statements. `pqf-def-locnoeth` supplies a covering with Noetherian section rings; clause (c) of `lem-weil-pbc-affine-open-stalk-localization` explicitly gives the localization's units, fractions and zero criterion; `lem-weil-pbc-localization-noetherian` assumes exactly that localization interface and concludes the target ring is Noetherian. Choosing a covering member containing each point therefore checks the stalk Noetherianity hypothesis instead of taking it from a definition alone.

For step 2 the statement of `def-weil-flat-morphism` supplies a flat local map on the actual stalks. The statement of `lem-weil-pbc-flat-height-formula` applies to any flat map of Noetherian rings and says the displayed localization dimension formula; specializing its primes to the two maximal ideals is legitimate because the map is local. The inverse localization is explicitly r/s -> r s^{-1}, since those denominators are units. The statement of `lem-sbc-scheme-fibre-stalk-quotient` gives the isomorphism with the actual scheme-theoretic fibre stalk, including uniqueness of the point. It does not merely define a fibre. Dimension invariance here follows directly by transporting prime chains along a ring isomorphism, as defined by the cited ring-dimension definition. Thus neither a tensor ring nor a point of another fibre is silently substituted.

For step 3 the homeomorphism clause of `def-pc-scheme-fibre` is what makes each fibre nonempty using surjectivity and identifies all of its points with the points in the hypothesis. `lem-weil-pbc-dimension-supremum-local-dimensions` applies to every topological space, so certainly to this fibre, and gives dimension d. `lem-pc-scheme-dimension-local-rings` applies to every scheme and supplies the second supremum with no smallness, Noetherian or quasi-compactness restriction. Ring dimension has the extended-natural values written in `def-weil-pbc-krull-dimension-ring`; a stalk is a nonzero local ring and so has a maximal prime. The attainment proof handles d=0 separately; for positive d the alternative upper bound d-1 contradicts the supremum. This fixes the possible confusion between local topological and local-ring dimensions.

For step 4 I reread the scheme-stalk supremum node: its statement really concerns the global topological dimension and allows infinite dimension. Apply it separately to source and target. The proof writes both inequalities, and explicitly checks that a finite nonempty integer-valued supremum is attained while an infinite one gives unbounded lower bounds (or an infinite term). The hypothesis that Y is nonempty excludes the empty-supremum exception; surjectivity then also excludes empty X. Local finite type is retained exactly as in the item, although these stalk and supremum arguments use only flatness, local Noetherianity and constant fibre dimensions. No global finite type, separatedness, Jacobson property or catenarity was added.

I checked B1-B10: no new nodes or proof sketches in statements, no missing introduced object or definition in the unchanged statement, ordinary single TeX commands in the added proof, tag/label sources, actual logged searches, no false Mathlib match or attachment, and the inherited precise blueprint ancestry retained with same_as checked. I checked C1-C8 by opening every cited statement as described above, generating all twelve literal quotes, and declaring the off-unit generic tools only in split_report.tool_uses. These are the algebra and dimension tools explicitly used by 0AFE, not a different unit route. I checked D1-D5: the proof carries the inequalities and the finite-supremum argument itself, creates no clause-restatement nodes, invokes no parent dependent on this item, and leaves no 'details omitted' instruction. I checked E1-E7 against the actual stalks and fibres: all ring hypotheses are verified, no affine-intersection assumption is used, and no statement dispute or source error was found.

Small-case checks were identity maps (d=0), nonempty zero-dimensional bases, affine space over a field including its generic point, disconnected bases with different component dimensions, and disjoint unions of affine spaces with unbounded dimension to exercise the infinite supremum. Removing surjectivity would invalidate the lower-bound step, which explains exactly where that hypothesis is used. An empty base is expressly excluded. No proof step exceeds 2000 characters (lengths 490, 894, 916, 1034); all remaining comparisons are explicit applications of cited statements or the written elementary fraction/finite-integer arguments. No Lean files, compilers, repository files or launcher files were changed.

The first dry run required a longer citation excerpt for localization Noetherianity (minimum 40 characters). I replaced the short concluding sentence with that node's whole statement, which also displays every localization hypothesis used in step 1. No mathematical proof change was needed.
