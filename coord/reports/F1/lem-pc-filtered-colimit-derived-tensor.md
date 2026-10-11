# Stage-1 split: lem-pc-filtered-colimit-derived-tensor

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-filtered-colimit-derived-tensor.json`: item split into four proof steps; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement excerpt per cited node in each step.

## Attachments

None. A search for the blueprint tag and the filtered-colimit/derived-tensor terminology in `WeilConjectures/` found no sorry-free project declaration stating the item.

## Sources and corrections

The local checkout has only `literature/CITATIONS.tsv`, `literature/stacks-tags-cited.tsv` and import tools; the Stacks `.tex` source is absent. I read the primary Stacks pages for Tags [06Y6](https://stacks.math.columbia.edu/tag/06Y6), [06Y0](https://stacks.math.columbia.edu/tag/06Y0), [064L](https://stacks.math.columbia.edu/tag/064L), [06YR](https://stacks.math.columbia.edu/tag/06YR), and [00DB](https://stacks.math.columbia.edu/tag/00DB). WANTED: local `literature/stacks-project/more-algebra.tex`, `sites-cohomology.tex` and `algebra.tex`, at those tags, for this item. The item's original source field incorrectly placed Tag 06YR in `more-algebra.tex`; it is in `sites-cohomology.tex` and states K-flatness of filtered colimits. Tag 06Y6 supplies the derived tensor functor, Tag 06Y0 the quasi-isomorphism argument, and Tag 00DB the homology calculation. The item statement is retained, including the previous review's cohomology-only correction. The proof is marked agent-written because it combines these sources into the present statement.

The inherited `lead_notes` sketch correctly resolves `M` over `R`, but that resolution is not an `A`-complex in general. Step 1 therefore compares only the underlying `R`-complex of the `D(A)` value to the fixed-resolution model. Step 4 recovers `A`-linearity from the canonical map itself, whose components are `A`-linear.

## Review by F1

I read the item's statement, its parent blueprint place, the chapter and unit records, and the five cited DAG statements. I checked Tags 06Y6, 06Y0, 064L, 06YR and 00DB against the four steps. The fixed-resolution comparison is justified at the level of `R`-complexes; it does not assume that an `A`-module admits an `A`-linear resolution by `R`-flat modules. For example, when `R=Z`, `A=Z/2Z`, `M=A`, that assumption would fail, while the underlying comparison still works. If `M=0`, every tensor and cohomology group is zero; if `I` has one object, the canonical map is the identity; if `N_i` are concentrated in degree zero, the result specializes to exactness of filtered colimits for Tor.

Step 1 uses `lem-pc-kflat-resolution` only for existence of a K-flat resolution over the one-point `R`-site. Clause (2) of `lem-pc-derived-tensor-second-factor-functor` computes the `D(A)` value by resolving its first, `R`-complex input. `lem-pur-quasi-iso-cone-acyclic` says exactly that a quasi-isomorphism has acyclic cone; `lem-pc-tensor-mapping-cone-iso` identifies the cone after tensoring; `def-pc-kflat-complex` makes that tensor cone acyclic. The sign swap for the right-hand arrow is the elementary symmetry of total tensor complexes, written in the step. No cited statement is asked to supply an `A`-action on the `R`-resolution.

Step 2 uses the canonical resolution-comparison clause of `lem-pc-derived-tensor-second-factor-functor` for independence of each auxiliary resolution of `N_i` and `N`. It uses the termwise tensor-colimit isomorphism stated by `lem-pc-module-filtered-colimits-tensor`, specialized to the small one-point site and the filtered diagram. The step identifies its structure maps with tensoring the actual coprojections; this is the point needed to recover the canonical map rather than an unspecified isomorphism.

Step 3 uses the exactness clause of the same module-colimit node, again on the one-point site. Exactness applied to the two differentials around degree `n` preserves kernels, images and their quotient. This is the explicit degreewise argument for Tag 00DB and needs no boundedness. Step 4 uses clause (3) of the derived-tensor functor node: a map of `A`-complexes induces the stated natural transformation. The displayed colimit map is assembled from `A`-linear coprojection maps, hence is `A`-linear; the same naturality squares give naturality in both variables.

I checked B1-B7: no new node exists, the item names its objects and TeX is serialized once, the corrected source tags have the right documents, and no Mathlib leaf is claimed. For C1/C4 I opened each cited statement, copied the exact part used into `citations.json`, and removed a redundant off-unit abelian-groups citation and a redundant roof argument during review. The only off-unit tool is the generic quasi-isomorphism/cone criterion, declared in `split_report.tool_uses`. I searched the DAG and the blueprint for the filtered-colimit, K-flat comparison and Tag 06YR facts; the relevant existing nodes cover the proof, so the split creates none. For E I checked the ring, algebra, small one-point site, K-flat and filtered-index hypotheses at their use sites, plus the three small cases above. The original source placement was corrected and the non-`A`-linear resolution issue was made explicit.

## Not duplicates

No new node was created.

## Unfinished

No mathematical step remains open in this split. The local Stacks `.tex` files remain unavailable in the read-only repository; the primary online tags were read instead.

## Second reading by F1

- Step 1: checked against the statements of `lem-pc-kflat-resolution`, `lem-pc-derived-tensor-second-factor-functor`, `lem-pur-quasi-iso-cone-acyclic`, `lem-pc-tensor-mapping-cone-iso`, and `def-pc-kflat-complex`; the two comparison maps are quasi-isomorphisms of underlying `R`-complexes, with no assumed `A`-linear resolution.
- Step 2: checked against `lem-pc-derived-tensor-second-factor-functor` clause (2) and `lem-pc-module-filtered-colimits-tensor`; the resolution comparison is natural in the diagram and the displayed chain maps are the coprojections.
- Step 3: checked against the exactness and tensor-colimit clauses of `lem-pc-module-filtered-colimits-tensor`; the degreewise kernel/image quotient argument proves the cohomology isomorphism for every integer degree.
- Step 4: checked against clause (3) of `lem-pc-derived-tensor-second-factor-functor`; the canonical map is assembled from `A`-linear maps and is natural in both variables.
- New nodes: none; therefore B1-B7, duplicate search, and Mathlib-leaf requirements introduce no new-node findings.

Changes made: corrected the item node's copied `created.item` metadata to `lem-pc-filtered-colimit-derived-tensor`; added this explicit second-reading checklist and recorded that the local `.tex` sources are unavailable while the cited online Stacks tags were checked.
