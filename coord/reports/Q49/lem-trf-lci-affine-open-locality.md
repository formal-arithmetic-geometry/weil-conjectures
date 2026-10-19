## Files written

- `dag/nodes/sec-trace-formula/lem-trf-lci-affine-open-locality.json`: split item with three proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-lci-pointwise-criterion.json`: new unsplit statement node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every step.
- `searches.jsonl`: Q49 Mathlib searches, including the item and new node searches.

## Attachments

None. I searched the read-only slopmaster2 and upstream sources for the item id, its title, local-complete-intersection terms, and the blueprint tag; no sorry-free declaration states the item. The live DAG item is unsplit, so this is a genuine split.

## WANTED

None. The cited Stacks sources are present in `literature/stacks-project/`.

## Corrections and scope

The imported item statement is mathematically sound and was retained, including empty schemes and the zero coordinate algebra. The item had no proof. I added one generic supporting node for the pointwise local-ring criterion (Morphisms Tag 01UG together with Algebra Tag 00SH); it is strictly more general than affine-open locality and is left unsplit. No definition or item clause was duplicated as a new node. The existing `lem-weil-pbc-lft-affine-pairs` is used as an off-unit tool in step 2 and declared in `split_report.tool_uses`.

## Not duplicates

lem-trf-lci-pointwise-criterion vs lem-trf-lci-affine-open-locality: the new criterion is an equivalence for any locally finite type scheme and its complete-intersection local rings, plus the affine algebra localization criterion; the item starts from a specified affine cover and concludes the coordinate ring of each affine open.

lem-trf-lci-pointwise-criterion vs lem-weil-pbc-lci-field-change: the criterion is local in the scheme/algebra and compares local rings with an lci algebra; field-change compares one finite-type algebra after extension of scalars.

lem-trf-lci-affine-open-locality vs def-weil-pbc-complete-intersection-over-field: the definition gives principal global-complete-intersection covers inside one finitely generated algebra; the item proves that arbitrary affine opens inherit this property from a scheme cover.

## What remains

The new pointwise criterion is statement-only and unsplit, as required for a newly created stage-1 node. No Lean source was written and no compiler, Lake, or build tool was run.

## Review by Q49

I read the item source references, Morphisms Tags 01UG (local complete intersection), 01T2 (locally finite type on affine pairs), and Algebra Tag 00SH (global lci iff all localizations are complete intersections), plus the existing definitions cited by the item. I also read the statements of every DAG node cited below. The affine cover by the $Z_i$ makes $Z\to\operatorname{Spec}k$ locally of finite type because each $C_i$ is finitely generated. Applying the new pointwise criterion to each $Z_i$ gives complete-intersection local rings; open restriction identifies these with the local rings of $Z$, so the hypothesis is available at every point.

For step 1, the cited pointwise criterion explicitly says that an affine-open lci cover implies every local ring is a complete-intersection local ring. The finite-type definition explicitly supplies the affine finitely generated cover used to establish local finite type. No quasi-compactness or separatedness was added.

For step 2, I checked the exact statement of `lem-weil-pbc-lft-affine-pairs`: for an affine source and affine target, local finite type is equivalent to finite type of the induced ring map. Applied to $W\to\operatorname{Spec}k$, it gives that $S=\Gamma(W,\mathcal O_Z)$ is finitely generated. The local rings of $W$ are the same as those of $Z$ at the corresponding points; the empty affine open gives the zero ring case.

For step 3, the algebra clause of the new criterion is exactly the 00SH equivalence: a finitely generated $k$-algebra is lci precisely when all prime localizations are complete-intersection local rings. Each such localization is a local ring of $W$, already checked in step 1. The complete-intersection definition supplies the zero-ring convention. Thus the conclusion includes both finite generation and the required local-complete-intersection property.

I tested the edge cases $Z=\varnothing$, $W=\varnothing$, a single affine lci scheme, and a nonreduced lci example such as $\operatorname{Spec}k[t]/(t^2)$. I checked the whole DAG and blueprint for 01UG, 00SH, local-ring criterion, and affine-open lci statements before creating the new node; no duplicate or cycle was found. The new node has its own LeanSearch, LeanFinder, Loogle, and Mathlib grep records, and the item has the required searches with their actual Q49 log entries. No step exceeds 2000 characters or hides a separate comparison lemma.
