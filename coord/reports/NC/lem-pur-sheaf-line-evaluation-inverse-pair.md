# Stage-1 report: lem-pur-sheaf-line-evaluation-inverse-pair

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-sheaf-line-evaluation-inverse-pair.json: split statement, unchanged, eight proof steps, no new nodes and no Mathlib leaves created.
- citations.json: verbatim statement quotations for all 22 step/node pairs.
- report.md: this report. searches.jsonl retains the searches actually run; write_split.py is a sandbox-only preparation script.

## Attachments

None. I searched lean/WeilConjectures/ for the exact blueprint tag and evaluation/inverse, locally-free/invertible concepts. InternalHomFree.lean has a dual-finite-locally-free theorem, but does not assert rank one, this specified evaluation inverse, and the inverse-pair identities. SixFunctors/Etale/Derived/LocallyConstantInvertible.lean treats constant coefficients on small étale sites, a strict special case of this arbitrary-ringed-site statement. Neither is an attachment for the item. No claim that a source declaration resting on sorry is complete is used here.

## Literature wanted

None.

## Problems found and changes made

The imported item was statement-only; its statement is correct. I preserved it verbatim, including the specified triangles, arbitrary sheaf of rings, all size assumptions, flatness, and B-linearity. I filled in Stacks 0B8Q's “details omitted” rather than introducing nodes for the item's own clauses. The current blueprint main-20261015 proof (3), last two sentences, explains the route: a locally trivial line has evaluation isomorphism, is flat, and gives inverse tensor twists. The existing blueprint ancestor and via list are retained. Blueprint searches “rank one”, “sheaf tensor”, “invertible”, and “equivalence preserves” find no blueprint node stating this full arbitrary-ring-sheaf, specified-inverse-pair statement; same_as stays empty.

The first new Loogle query, “SheafOfModules, IsIso”, returned unknown identifier IsIso. I recorded that result and then searched the valid name SheafOfModules.unitHomEquiv; that returned six free/unit-Hom declarations. LeanSearch and two LeanFinder phrasings returned free-sheaf Hom APIs and ordinary module Picard theory. I read Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:178–193, Sheaf/Free.lean:61–72, and RingTheory/PicardGroup.lean:81–110: these do not supply the whole sheaf statement by one-line specialization. The required logged grep searched Algebra/Category/ModuleCat/Sheaf for IsInvertible|evaluation|ihom.ev and returned only Limits and Free evaluation-functor references. All appended query texts match searches.jsonl. Inherited Mathlib search records were retained separately, with their original unavailability recorded unchanged.

## Not duplicates

No new nodes. The general tools already exist, so no separate “dual of a line”, “evaluation isomorphism”, “tensor inverse equivalence”, or “triangle identity” node was created. lem-pc-sheaf-modules-tensor-closed supplies structural tensor constraints, lem-sfb-localized-site-tensor-restriction supplies the normalized slice comparison, lem-pc-sites-sheaf-tensor-bilinear-universal supplies the mapping property, and lem-galois-equivalence-preserves-limits supplies limit/colimit preservation. The item does not cite its parent or blueprint ancestor as a proof dependency.

## Unfinished work

None at stage 1. No Lean code was written, no compiler or Lake invoked, and no repository or launcher file changed. All writes are confined to this item's sandbox.

## Review by NC

I read the item against Stacks sites-modules.tex Tag 0B8Q (lemma-invertible-is-locally-free-rank-1), its first proof paragraph, and Tag 0B8N (lemma-invertible), its statement and first two proof paragraphs. Only the implication from locally free rank one is used; the converse's locally-ringed hypothesis is not needed or assumed. I also read the current blueprint sk-def-sp-tate-twist-locally-free.proof.md paragraph (3), the recorded chapter and sk-prop-an unit, and the three-level route rules. This split supplies the ordinary sheaf-line tool for that route and makes no claim to establish its parent's unbounded derived-category conclusions.

I opened and read the statement of every cited node. Step 1 uses def-pur-sheaf-hom's slice-Hom description and def-pur-localized-ringed-site's relocalization, so restriction of the dual is justified by identical slice categories. A local linear map is determined by its value on p; the displayed inverse proves rank one, and inverse coordinate changes prove the unit condition and inverse transition. No general finite-projective-dual theorem is assumed.

Step 2 uses precisely the bilinear-pairing bijection in lem-pc-sites-sheaf-tensor-bilinear-universal to construct evaluation and to test the local inverse equations. lem-sfb-localized-site-tensor-restriction states both the tensor comparison and its normalization on original pure tensors. That normalization is essential: it justifies the actual local formulas for the global evaluation map. I checked its source, Stacks 03EL (lemma-tensor-product-pullback), with localization 03DH (section-localize, definition-localize-ringed-site), where the coefficient-ring map is the identity. There is no flatness or constant-coefficient assumption in the cited node.

Step 3 uses the sheaf and global-section assertions of lem-pur-sheaf-hom-is-sheaf to glue local inverse morphisms and check the two inverse equations. Its statement really concerns module-sheaf maps on slices, rather than merely a set of sectionwise maps. Compatibility is proved by the change-of-basis tensor equation and, on any refining slice, uniqueness of an inverse. This avoids assuming that pairwise fibre products exist. Global compatibility under restriction follows from uniqueness of sheaf amalgamation, as written in the step. I do not cite effective descent of objects here.

Steps 4 and 5 use the actual section-induced associator, symmetry, unitors and additivity stated in lem-pc-sheaf-modules-tensor-closed. They define a and b in the required order; evaluation after symmetry is used in b. Their inverses are computed from the previously constructed e inverse, not chosen from an unspecified equivalence. I checked naturality by the bifunctor equation written in step 4. Step 5 spells out balancing for the inverse equations and for invariance under a basis change. The bilinear universal property and normalized slice comparison are explicitly cited for the tensor-map equality test.

Step 6 evaluates the first triangle on x tensor cp and the second on x tensor dp dual. The intermediate tensor orders are written out; they return respectively x tensor cp and x tensor dp dual. Its cited statements supply equality testing, normalized restriction, and separatedness of the Hom sheaf, respectively. No coherence theorem claiming these triangles automatically from arbitrary inverse-equivalence choices is smuggled in. Steps 1, 4, 5, 6 and 8 are elementary coordinate/definition arguments once their named interfaces are supplied; steps 2 and 3 are explicitly non-elementary applications of those interfaces.

Step 7 applies lem-galois-equivalence-preserves-limits only after a and b have exhibited a genuine equivalence. I read its entire statement: it preserves existing limits AND colimits, for arbitrary diagram shapes. The site's relative smallness makes the module category abelian by def-weil-sheaf-of-modules-category; finite limits and colimits therefore exist. The named generic result covers the finite shapes required here. I read Categories 0038 (lemma-adjoint-exact) for the source route. Preservation of kernels and cokernels yields exactness in an abelian category, and def-pc-flat-sheaf-modules defines flatness by precisely this tensor exactness. Tensor additivity comes from the structural tensor node, so it is not inferred from an arbitrary nonadditive equivalence.

Step 8 uses def-weil-linear-functor's explicit additivity and scalar-action criterion. For a B-algebra sheaf the images c_U of a fixed scalar commute with restriction. The written equations establish linearity on Hom sets using the tensor bilinear universal property; all components and their inverses are R-linear module-sheaf maps, hence B-linear. Nothing requires R to be a constant ring sheaf or P to have a global basis.

I tested the statements and formulas on the one-object trivial site (ordinary free rank-one modules), a line with nontrivial transition units, the zero ring (where 1=0 and the unique module is zero), M=0, and slices admitting an empty covering sieve. In the last case the sheaf axiom forces a unique section and every equality still holds. The cover/sieve formulation covers sites without fibre products and without enough points. All scalar cancellations use units, never nonzero-element cancellation. Every proof step is under 1000 characters, so no step crosses the 2000-character hidden-lemma threshold. No statement dispute or source correction was needed. No SGA source is used.

The off-unit structural tools are declared in split_report.tool_uses with their purposes; they provide general module/sheaf interfaces and do not replace any step of the unit's purity route. I checked B–E explicitly: self-contained original statement, no new-node form or duplicate issue, no unstated theorem behind a tag, exact statement quotations in citations.json, no cycle through the parent, no added local-ring/point/fibre-product hypothesis, and no clause repackaged as a new lemma.
