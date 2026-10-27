# Stage-1 report

## Files written

- dag/nodes/sec-smooth-purity/lem-route-site-sheaf-tensor-right-preserves-zero-morphisms.json: statement, split into three elementary steps; no exact Mathlib match.
- citations.json: verbatim statement excerpts for all four step/node pairs.
- report.md: this report. The search command generated searches.jsonl.

No new nodes, and no new Mathlib leaves.

## Attachments

None. The declaration SheafOfModules.siteSheafTensorRight_preservesZeroMorphisms in lean/Sheaf/Algebra/Category/ModuleCat/Sheaf/SiteTensorFunctoriality.lean:37 still has `sorry`. Searching WeilConjectures/ by the blueprint tag and by tensor/zero-preservation concepts found no declaration of precisely this independent-universe, varying-ring module-sheaf functor. The additive tensorRight instance for ordinary sheaves valued in a fixed abelian monoidal category is a different construction, and does not supply an attachment for this item.

## WANTED

None. The sources used are present.

## Corrections and provenance

The machine-generated statement was a Lean signature preceded by its docstring, with no introduced site, coefficient sheaf, size assumptions or dependencies. I replaced this presentation with a complete statement of the same theorem. It retains the three class hypotheses from SiteTensorFunctoriality.lean:28-32: composition with the ring forgetful functor, weak abelian-group sheafification in the module universe, and equality of the inverted morphisms with the locally bijective ones. Site, ring, and module universes remain independent; no smallness, enough-points, flatness, field, nonzero-ring or finite-generation hypothesis was added. The zero-preservation assertion itself was not changed. This is not a statement dispute.

The generated source field pointed to proetale.tex, whereas the docstring's actual source is Modules on Sites, Tag 03EK (sites-modules-section-tensor-product). I corrected the source and also cited Tag 03CY (sites-modules-lemma-sheafification-presheaf-modules) for unique factorization. Stacks defines the tensor but does not print this exact zero-map proof; proof_origin is therefore agent. No SGA source is used.

Read the chapter and unit records. The item is not a unit key statement and no realized record is changed. Its recorded ancestor def-weil-rationalization-karoubi has no file bearing that id in literature/blueprint/latest/blueprint/. I read its DAG statement (final paragraph on integral scalar extension followed by rationalization) and retained the inherited ancestor and via list. The tensor definition is present in the current snapshot at sec-curve-estimates/sk-def-pbc-conventions/def-pur-sheaf-tensor-product.md and agrees with the cited DAG definition. The proof supplies zero preservation needed on the recorded tensor-complex route, without altering a unit or chapter.

## Searches and Mathlib verdict

All added Mathlib search entries come from actual msearch.py invocations logged in searches.jsonl; the old maintainer-generated name search is retained as history. Read the returned hits, including TensorProduct.map_zero_left, LinearMap.rTensor_zero, preservesZeroMorphisms_of_additive, tensorRight_additive, plusPlusSheaf_preservesZeroMorphisms, and the module-presheaf tensor and sheafification constructions. These are component statements or require an already established additive/monoidal identification; none states the explicit composite siteSheafTensorRight with its independent ring/module universes. The unsuccessful first Loogle pattern reported an unknown identifier; that diagnostic is preserved, and a second valid pattern TensorProduct.map_zero_left returned its expected component lemma. Two natural-language phrasings were tried. No service outage was relabelled as absence.

The resulting proof needs no new node for any of these component facts: it writes the tensor zero calculation and the sheafification uniqueness argument explicitly as elementary steps. Before deciding this I searched dag/nodes for zero/tensor/sheafification concepts and 03EK, and used blueprint_refs.py search with tensor, 03EK, and sheaf tensor right zero morphisms; the latter two searches returned no blueprint matches. blueprint_refs.py ancestor confirmed the inherited ancestor. There is no duplicate new node to compare.

## Not duplicates

No new nodes were created.

## Unfinished work

None for stage 1. No Lean file was written or compiled, and the existing Lean proof remains a later-stage task.

## Review by NJ

I read Stacks sites-modules.tex at the tensor definition (Tag 03EK) and the complete statement and surrounding adjunction paragraph of the module-sheafification lemma (Tag 03CY). I also read the existing Lean functor definition in TensorProductOfUniverses.lean:363-382: it is precisely forget, then siteTensorRight N.val, then PresheafOfModules.sheafification at the identity coefficient morphism. The identity is locally injective and locally surjective by the preceding declarations; there is no change of coefficient ring hidden in the argument. SiteTensorFunctoriality.lean confirms both the theorem's hypotheses and its remaining sorry. The newest blueprint tensor definition was read against the DAG definition.

For step 1 I opened def-weil-sheaf-of-modules-category and def-pur-sheaf-tensor-product. The first states that morphisms are sectionwise linear; the second gives exactly the sectionwise tensor and its sheafification. The step uses these only to identify the components of the map being computed. It then gives the elementary calculation on pure tensors, cancellation proving zero tensor y is zero, and generation by pure tensors from the algebraic tensor construction. Equality of the components gives equality of presheaf morphisms. No exactness, stalk, monoidal-category comparison or additivity-of-tensor theorem is assumed.

For step 2 I opened def-weil-presheaf-modules-sheafification. Its statement explicitly supplies a linear unit and unique factorization of every map to a module sheaf, not merely the existence of a sheafification. Both the sheafification of the zero map and the zero sheaf map have the same zero composite with that unit, by naturality and composition of linear maps. Uniqueness therefore identifies them. This is why a new generic sheafification-additivity theorem would be unnecessary: the needed assertion is two lines from the already cited universal property.

For step 3 the cited tensor definition states that the sheaf tensor is the sheafification of the sectionwise tensor. The step substitutes step 1 into step 2. All cited assertions occur in the statements themselves, and citations.json quotes their exact text. Every step is short (under 700 characters), elementary with the details written, and no hidden non-elementary comparison has been substituted for a cited statement. All used nodes exist and are definition nodes, so there is no off-unit proof-tool declaration and no dependency on the item from its proof dependencies.

I checked the B--E failure modes against these files: there are no new statement-only nodes, duplicate nodes, restatements delegated to new nodes, unproved inline lemmas, or missing non-elementary citations. The complete argument works for the empty site, a zero ring sheaf, zero M or N, and the ordinary one-object module situation; it never divides by a scalar or assumes nonzero sections. Sheafification uniqueness works even when local sections or enough points are unavailable. The independent module universe is unchanged throughout: the tensor of two modules in that universe remains there, so the given sheafification hypotheses apply. The generated source mismatch and missing setup were corrected as described above.
