# Stage-1 report: lem-sfb-qcqs-space-pushforward-right-adjoint

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-space-pushforward-right-adjoint.json`: item, split into four steps proving the stated restriction, Brown adjoint, and counit formula. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-compact-perfect-generator.json`: new statement-only lemma; compact perfect generator detecting zero by all shifts, Stacks 09IY and 09M8. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-pushforward-coproducts.json`: new statement-only lemma; unbounded qcqs direct image preserves quasi-coherent cohomology and the canonical coproduct comparison is an isomorphism, Stacks 08FA(1), 08FB, 08F3. No Mathlib match.
- `citations.json`: nine verbatim statement excerpts, one for every dependency of every proof step.

## Attachments

None. Searching the project's `lean/WeilConjectures/` for the item's blueprint tag and the derived quasi-coherent/adjoint notions found no declaration for algebraic spaces. `AlgebraicGeometry.schemeDerivedDirectImage_qcqs_hasRightAdjoint`, at `WeilConjectures/AlgebraicGeometry/QCqsDerivedDirectImageRightAdjoint.lean:55`, is for schemes and ringed spaces, not arbitrary algebraic spaces and their small etale sites. It does not attach to this item. The generic K-injective triangulation theorem is already recorded on `lem-pc-right-derived-functor-triangulated`; its instances at lines 94 and 97 were read and reused, not duplicated.

## WANTED

None. All mathematical sources needed here are present under `literature/stacks-project/`.

## Corrections and provenance

The item's mathematical assertion agrees with Stacks 0E55 (`spaces-duality.tex`, `lemma-twisted-inverse-image`) and the formula in `section-trace`. No mathematical hypothesis or conclusion has changed. I made the existing fixed-universe convention and canonical small-etale module functors explicit in the statement and `stmt_deps`. The original K-flat pullback convention remains, although this proof only uses direct image.

The inherited `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor` also returns None because the creation chain has no imported blueprint ancestor available. I retained that computed value and its existing via chain, and filled precise supporting-input places for the new nodes. Searches over the whole imported blueprint for Brown, compactly generated, perfect generator, derived coproducts, algebraic-space derived categories, and tags 08FA, 08FB, 09IY and 09M8 give no equivalent blueprint node for either new lemma. The generic Brown statement already exists and is cited.

I read the latest blueprint at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` (frontmatter id `det-thm-sf-ctf-stability-direct-images`). Its paragraph (3) now argues via compactification and proper/open preservation. It no longer states the alteration paragraph named by the creation chain of this item. This is a provenance mismatch upstream of the assigned node, not a false coherent-duality statement. The inherited historical place is retained and the current difference is recorded in `split_report.blueprint`; no chapter, unit or other node was edited. This item only supplies its parent's coherent-duality construction prerequisite.

## Searches and the level of the split

All new Mathlib searches were run through the specified `batch2/msearch.py` and are in `searches.jsonl`. Each new node and the item has LeanFinder with two different phrasings, Loogle, grep, and LeanSearch. Raw service output is retained as `search-*.txt` and copied into the relevant new search entries. All services answered. I read the hits: ordinary scheme-module and sheaf-module pullback/pushforward adjunctions are the adjunction in the other position, not a right adjoint to unbounded derived quasi-coherent pushforward; generic `DerivedCategory` constructors and quasi-coherent presentations do not assert a compact generator. The two Bondal/Van den Bergh grep hits are bibliographic references in `Mathlib/CategoryTheory/Triangulated/Generators.lean`, which defines abstract triangulated envelopes, not a theorem about algebraic spaces. I also read scheme-module pullback/pushforward in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:189-200` to check that mismatch. Older search entries on the item were retained as historical material; their hits were read.

Before adding the nodes I searched the whole DAG by all source tags, labels and keywords, and the project Lean source. The existing localizing-generation lemma supplies coproduct existence but does not assert that a perfect object is compact or that one compact object detects zero. Conversely a compact generator statement does not restate localizing generation or this item's adjoint. The new pushforward input applies to general qcqs morphisms, without individual spaces being qcqs, gives the canonical sum comparison, and does not assert an adjoint. Neither new lemma is an adjoint-existence clause repackaged. The steps do the categorical assembly and write out the counit calculation. No non-elementary step exceeds 2000 characters; the whole assembly is under 3000 characters.

## Not duplicates

lem-sfb-space-compact-perfect-generator vs lem-sfb-space-perfect-localizing-generation: the existing 09IY-citing statement asserts localizing generation by all perfect objects and ambient coproduct closure; it asserts neither compactness nor existence of a single compact zero-detecting object. The new node states those two missing assertions, using 09M8 as well as 09IY. The existing statement is used for coproducts and inherited cones rather than silently taking compactness from its source reference.

lem-sfb-space-compact-perfect-generator vs lem-pc-perfect-generator-exists: the existing statement is for schemes; the new statement is for arbitrary algebraic spaces and their small etale structure sheaves, and includes compactness.

lem-sfb-space-compact-perfect-generator vs lem-pc-derived-qcoh-compact-generation: the existing statement is for qcqs schemes, while the new one allows arbitrary qcqs algebraic spaces and specifies a single perfect compact detector.

lem-sfb-space-derived-pushforward-coproducts vs lem-pc-derived-direct-image-preserves-direct-sums: the existing statement is for scheme morphisms (08DZ); the new one is for arbitrary algebraic-space morphisms on their small etale sites (08FB) and includes quasi-coherent preservation (08FA).

lem-sfb-space-derived-pushforward-coproducts vs lem-sfb-flat-space-derived-pushforward-base-change: that existing statement requires flatness and asserts a canonical base-change isomorphism, not preservation of arbitrary coproducts for every qcqs morphism. No flatness is assumed in the new node.

lem-sfb-space-compact-perfect-generator vs lem-sfb-space-affine-pullback-perfect-detection: the existing statement concerns a morphism C \to D on the source of an affine map h, tested by all shifted Hom groups out of pullbacks of perfect objects from its target. It asserts neither existence of one perfect generator on a qcqs algebraic space nor compactness of that generator. Its 09IY source reference therefore does not supply the statement needed for Brown representability.

## Review by Q46

I read `spaces-duality.tex`, 0E55 and `section-trace`, and checked the item's domain, codomain, and the direction of both adjunction Hom sets against them. Both X and Y are qcqs; S is an arbitrary scheme. No Noetherianity, properness, finite presentation, or flatness entered. In particular I did not apply a theorem for a bounded derived category to an unbounded object.

For step 1 I opened `lem-sfb-space-qcqs-permanence`: it explicitly gives quasi-compactness of f from X quasi-compact and Y quasi-separated, and quasi-separatedness of f when X is also quasi-separated. This is exactly Stacks 073B(1)-(2), which I read in `spaces-morphisms.tex`. I then read 08FA(1), 08FB and 08F3 in `spaces-perfect.tex` for the new pushforward statement. These assert preservation of quasi-coherent cohomology for unbounded inputs and invertibility of the comparison induced by sum injections for every qcqs morphism; they do not require properness. I opened `lem-sfb-space-perfect-localizing-generation` and used only its actual closure under ambient sums, shifts and cones, separately for X and Y. The triangulation is inherited from the ambient derived category, whose triangulated structure is explicitly stated by `def-weil-abstract-derived-category`.

For step 2 I opened `def-trf-space-etale-module-functors`: its actual sectionwise limit formula defines the canonical module direct image, so addition of module maps is preserved by its projections and universal property. No adjoint on the derived quasi-coherent subcategory is smuggled in here. I opened `lem-pc-right-derived-functor-triangulated`; its statement grants shift compatibility and preservation of distinguished triangles for additive K-injective right derived functors, exactly what is used. Its project instances at lines 94-99 are sorry-free. Restricting an already triangulated functor to the full triangulated subcategories from step 1 preserves their triangles by their definition.

For step 3 I read 09IY (`theorem-bondal-van-den-Bergh`) and 09M8 (`proposition-compact-is-perfect`). The former supplies the perfect object P with vanishing Hom(P[n],E) detecting E=0, and the latter makes this same P compact under the same qcqs hypotheses. These are the assertions of the new generator node. I opened `def-pc-compactly-generated` and `def-pc-generators` to check the sign in the shift conversion: Hom(P[n],E)=Hom(P,E[-n]), so P's singleton family satisfies the weak-generator convention already used by the existing Brown node. I opened `lem-pc-brown-representability-right-adjoint`, whose statement requires exactly a compactly generated source, triangulated exactness, and preservation of set-indexed coproducts. Steps 1 and 2 establish the other hypotheses. Its source is derived.tex 0A8G (`proposition-brown`), which I also read. It is declared in `split_report.tool_uses` because it is a generic category-theoretic tool from the Picard unit, not a replacement of a unit proof route. I did not set the maintainer's `tool_uses` field.

For step 4 the formula is proved by applying naturality in E to u and the identity at a_f(F). The counit is defined as the transpose of that identity. This is an elementary calculation in the adjunction just obtained; no second adjoint-normalization lemma is hidden in it. I checked the direction against the displayed formula in `section-trace`.

I checked B--E with the files open: both new nodes are self-contained statements only, with empty proof/proof_deps, explicit universes, definitions for module sheaves/quasi-coherence/derived categories, and inline meanings of perfect and qcqs. The Stacks tags were confirmed in `stacks-project/tags/tags`. All cited statement excerpts are copied verbatim and asserted to be substrings before `citations.json` is written. Neither new node depends on the item. Tests of the small cases: for the empty space the derived category is zero and P=0 is compact with the asserted zero detection; for an affine scheme Spec A, A[0] is the usual compact generator; for an identity morphism the coproduct map is identity, and for an empty source both sides are zero. A nonproper affine morphism and arbitrary non-Noetherian affine rings remain allowed. The empty indexing family gives zero on both sides. These checks exclude accidental nonemptiness, properness or finiteness hypotheses. I corrected an initially unnecessary finite-cohomological-bound clause out of the new coproduct node so its final statement contains only the input used here. No mathematical statement dispute was found.

On resuming after interruption, the current DAG contained the additional 09IY-citing node `lem-sfb-space-affine-pullback-perfect-detection`. I opened its whole statement: its affine-pullback isomorphism-detection criterion has no compactness or single-generator existence conclusion. I added the explicit nonduplicate comparison above; the proof and new statements required no change.

## Validation

Server review and the required delivery dry run are run after this report. No Lean files, compilers, Lake commands or local DAG/preflight checkers were used. Only the assigned sandbox was written.
