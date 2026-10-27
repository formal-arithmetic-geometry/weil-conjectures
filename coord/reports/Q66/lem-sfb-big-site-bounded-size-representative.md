# Q66 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-big-site-bounded-size-representative.json: item, statement, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/def-sfb-stacks-big-site-category.json: new definition, unsplit; no Mathlib match. Specifies the full underlying-category admissibility condition in Stacks 021R(2)/000J(1)--(4), not an existence theorem.
- citations.json: verbatim statement excerpts for each of the item's three citations.
- searches.jsonl: actual msearch results, retained without modification.

## Attachments

None. Searched lean/WeilConjectures by the item's blueprint tag and by big fppf site, bounded size, size bound, 000J and admissible category. The Picard affine-site and restriction files concern covering-density of affine objects, not this closure condition. No finished declaration states the item or the new definition.

## WANTED

None. Sources are local Stacks sets.tex and topologies.tex, and the current literature/blueprint/latest tree.

## Statement and route audit

The mathematical statement is unchanged. Its existing phrase "chosen underlying full category" now explicitly cites the missing selection-convention definition. Stacks topologies.tex, Tag 021R, definition-big-fppf-site (2), defines that choice to be a category Sch_alpha as in sets.tex, Tag 000J, lemma-construct-category. Conditions (1)--(4) in that lemma are requirements on the selected ordinal. Its clause (2) is precisely the representative property here. Thus the item is an elementary extraction of data already required by the definition of a big site. It does not require rebuilding the transfinite existence proof of 000J or finding a representative in an arbitrary small full scheme category.

The older def-pc-fppf-site describes the relative site and its coverings, and refers to a chosen big ambient site, but does not spell out the 000J choice. That is why a definition node is needed. The new node records all four requirements, the rank hierarchy, and the allowed skeleton convention; it asserts neither that such a category exists nor an extra theorem about its objects. A theorem restating item clause (2) was deliberately not introduced. Its existence is an assumption in what a chosen Stacks big site means.

Read the current latest blueprint def-pc-fppf-site.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This item is a downstream size prerequisite on the effectivity branch and leaves the unit's direct-image route intact. The inherited blueprint.from.node is null, as printed by tools/blueprint_refs.py ancestor, because that imported ancestor no longer has a blueprint id; its complete inherited place and via chain are retained, and the new definition extends that exact place. The blueprint searches for bounded size, Sch_, countable, 000J, and admissible scheme category found no same-statement blueprint node. DAG source-tag and concept searches found no existing admissibility definition. The existing def-sfb-scheme-cardinal-size is reused rather than recreated.

## Mathlib searches

All searches were run through the required msearch command for Q66 and this item; their exact queries and actual result records are in the node files and searches.jsonl. Both the item's concept and the new definition were searched with LeanFinder, Loogle, LeanSearch and grep; a second semantic phrasing checked abstract closure constructions. No service failure was converted into absence. Read Mathlib/CategoryTheory/ObjectProperty/Small.lean lines 100--142: abstract essential smallness supplies a small representative property for an already essentially small class; it does not specify 000J admissibility. Read Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean lines 45--92: the essentially-small instance is for affine etale objects over a fixed base, not arbitrary bounded-size schemes. Read Sites/Small.lean lines 160--164: the smallGrothendieckTopology is a topology on a morphism-property over-category. Read Cover/MorphismProperty.lean lines 234--235: small precoverages bound covering-index types, not the objects of a rank-small full category. Countable-category and abstract colimit-cardinal-closure hits do not define the additional scheme-size closure condition. None is a one-line specialization giving the item or definition.

## Not duplicates

def-sfb-stacks-big-site-category vs lem-sfb-big-site-bounded-size-representative: definition of the selected category, including all four 000J admissibility conditions and 021R's use of them, versus the elementary extraction of one required condition for a fixed site.

def-sfb-stacks-big-site-category vs lem-sfb-big-site-open-cover-size-closure: definition of admissibility versus the estimate and representative consequence for schemes covered by boundedly many bounded-size opens.

def-sfb-stacks-big-site-category vs lem-sfb-bounded-affine-lft-coproduct: definition of admissibility versus a coproduct representative constructed from boundedly many quasi-compact locally finite-type schemes over affine opens of a fixed base.

def-sfb-stacks-big-site-category vs def-pc-fppf-site: the latter describes relative-site objects, morphisms and fppf coverings and leaves the ambient scheme-category choice implicit; the new definition supplies exactly that missing selection convention and does not redeclare a topology.

def-sfb-stacks-big-site-category vs def-sfb-scheme-cardinal-size: the latter defines only s(X); the new definition uses it and defines the admissible underlying category.

## Review by Q66

I read sets.tex, section-categories-schemes, the size definition, equation-bound, and the entire statement and proof of Tag 000J (lemma-construct-category). I also read topologies.tex Tag 021R (definition-big-fppf-site), especially its instruction in (2) to take any category constructed as in 000J. The source makes bounded-size closure part of the choice, so the new definition does not conceal an unproved lemma: it records the admissibility predicate on the already chosen object. The separate transfinite argument proves existence of such choices, which the fixed-site hypothesis has already supplied. All four requirements in the new definition match the source; countability concerns objects and morphisms, and the existence comparison for limits/colimits is with the category of all schemes, only when they exist. No global existence of all countable scheme colimits is asserted.

Step 1 cites def-sfb-stacks-big-site-category for the meaning of the selected category. Its statement explicitly says a big-site choice satisfies (1)--(4), so no definition node is being used for an unstated theorem. Step 2 cites the same statement's full condition (2), with S=T and W=Z. The object T is given in the original category, the precise size inequality is a hypothesis of the item, and the isomorphism is reversed explicitly to obtain the required orientation. Neither membership of Z nor a newly selected site is assumed. Step 3 cites its full-skeleton convention, which states there is an isomorphic representative for every original object; composition gives a representative in the originally fixed skeleton. These are direct applications of the defining requirements, so elementary=true is justified. Step 4 uses no node: the displayed maximum in the item and the empty-cover sheaf axiom give s(empty)=aleph_0, and the successor term bounds aleph_0. It has no non-elementary input.

I reopened every statement dependency: def-pc-scheme supplies schemes and their morphisms; def-weil-size-convention supplies universe/skeleton conventions; def-sfb-scheme-cardinal-size supplies the exact cardinal invariant; def-pc-fppf-site supplies the big-site/relative-site terminology; def-weil-pbc-category-colimit supplies colimits. Limits and the cumulative hierarchy are defined inline in the new node, so its statement is self-contained. No statement-only node contains a proof or proof dependency. There is no claim of an isomorphism-invariance theorem for s: the skeleton argument uses T itself in the ambient category and does not need one.

Small cases checked: the empty scheme has size aleph_0, a finite affine scheme still has size aleph_0 by the maximum, T=empty causes no exception, Z=T is included, a strict inequality may be equality at B(s(T)), and a full skeleton may omit Z literally while still containing its representative. An arbitrary full subcategory consisting of one unrelated scheme would fail condition (2), but is excluded by 021R; the new definition prevents that invalid reading. The universe convention places cardinal bounds and representatives in the allowed larger universe. The site topology never enters the proof beyond specifying the underlying-category choice. No statement dispute or source error was found. The only correction is making the implicit category-choice convention explicit and handling the skeleton and empty-scheme cases rather than hiding them.

Checked B--E of delivery-errors: definition is statement-only, TeX is singly escaped, its objects/hypotheses and the universal meanings of limits are introduced, Stacks tags and labels match local source, no Mathlib leaf is claimed, every citation uses its statement with an exact quotation in citations.json, no new statement restates a conclusion, and no cycle is introduced. Each elementary proof step is below 2000 characters and the assembly is short. No SGA route or source is used. I performed this direct-delivery review myself as required; no additional agent was started.

## Unfinished work

None for this stage-1 item. The new admissibility definition remains statement-only unsplit for subsequent processing as instructed for new nodes. Server checks and push follow this report.
