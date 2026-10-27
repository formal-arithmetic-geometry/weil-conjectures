# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bounded-affine-lft-coproduct.json: item split into four steps; statement and statement dependencies retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-qc-lft-scheme-size-bound.json: statement, unsplit; no Mathlib match for the scheme-size estimate.
- dag/nodes/sec-six-functors-basics/lem-sfb-big-site-open-cover-size-closure.json: statement, unsplit; no Mathlib match for membership in the fixed bounded category.
- citations.json: verbatim statements for every dependency used by every item proof step.

## Attachments

None. Searched the live lean/WeilConjectures source by the item's blueprint tag and affine/coproduct/bounded terminology, and by the new-node ids, Stacks tags and size terminology. No declaration states all the clauses of the item or either general size lemma. The finite coproduct and affine normalization declarations do not assert membership in a fixed big site. No Lean was written or compiled.

## WANTED

None. All the mathematical sources needed here are in literature/stacks-project/.

## Findings and corrections

The imported item had no proof. Its statement is correct with “big fppf site” understood as in its cited Stacks definition: a full category chosen by the Sets construction, not an arbitrary small full subcategory with an fppf topology. I read topologies.tex definition-big-fppf-site (021R) and definition-big-small-fppf (021S) to check this distinction. Objects of the slice need not themselves be fppf over T; flatness and local finite presentation concern coverings.

I retained the bound on J, including the explicit maximum with aleph_0. I did not replace “locally of finite type” by “finite type”: an affine source over an arbitrary non-quasi-separated base need not give a quasi-compact morphism. The general estimate 04T7 assumes only a quasi-compact source, exactly what is available.

The empty-cover edge case of the printed 000Q formula needs care: if I is empty then the displayed right hand side max(|I|,sup_i size(S_i)) is zero whereas size(empty)=aleph_0. Our closure node states the correct empty-cover conclusion; this follows directly from 000J(2), since aleph_0 is at most Bound(size(T)). No false empty-cover size inequality is used. This is a source edge-case issue, not a dispute of the assigned item. One could instead state the cover inequality with an additional aleph_0 in the maximum.

The ancestor command prints blueprint.from.node = None for this assigned item. I preserved that inherited provenance and prepended this item to the via chain for each new prerequisite, as instructed. The newest blueprint is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/; I read its _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3). This item serves the inherited descent/atlas prerequisite chain below that paragraph; the paragraph itself is not a source for cardinal closure. It does not restate either new node. No unit realization changes are appropriate for this subordinate item.

## Mathlib and duplicate searches

All new searches were run through the required msearch.py command, with full command results read and corresponding records retained in searches.jsonl. The item and each new lemma have LeanFinder, LeanSearch, Loogle and grep searches, plus a second semantic phrasing. The services answered successfully. The item searches returned finite scheme coproducts, affine morphism coproducts and construction of locally ringed-space coproducts, not the chosen-category assertion. The size-estimate queries returned affine covers and finiteType_appLE, not cardinal bounds on all affine opens and section rings. The closure queries returned open-cover and precoverage definitions; Scheme.AffineEtale.instEssentiallySmall addresses affine etale objects only.

I read Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:147–168, especially essentiallySmall_costructuredArrow_Spec (line 153), which proves essential smallness of affine locally finite type objects but not their cardinal bound relative to a fixed Stacks category. I also read Sites/AffineEtale.lean:40–60 and Sites/Fpqc.lean:35–54. A general universe-smallness theorem would not by itself establish the exact Stacks size closure; no candidate specializes to these two statements in one line.

Whole-DAG source-tag searches for 04T7, 000Q, 000J and 000R found the item and lem-weil-pbc-affine-etale-essentially-small-cover; I opened both statements. Searched the entire DAG for scheme-size, bound-finite-type, bound-size, what-is-in-it and the proposed ids. Blueprint searches used size, size of, bounded size, scheme size, affine locally, open covering, 000R, 04T7 and big fppf, with finite type and coproduct for the broader context. None states either new general lemma. Existing generic coproduct and spectrum quasi-compactness nodes were reused rather than recreated.

## Not duplicates

lem-sfb-qc-lft-scheme-size-bound vs lem-sfb-bounded-affine-lft-coproduct: the new lemma bounds the affine-open/section-ring size of every quasi-compact locally finite type source over any scheme; it says nothing about a coproduct, index family, big site or slice representative. The item combines it with a separate size-closure statement.

lem-sfb-qc-lft-scheme-size-bound vs lem-weil-pbc-affine-etale-essentially-small-cover: the existing statement asserts essential smallness and cover density for affine etale objects; it does not state a size inequality, does not cover all quasi-compact locally finite type sources, and cannot supply the bound taken in step 1.

lem-sfb-big-site-open-cover-size-closure vs lem-sfb-bounded-affine-lft-coproduct: the new lemma is the general bounded-open-cover criterion in a fixed big category; it assumes bounds on the sizes of the opens and their index set, permits overlapping non-affine opens and requires no locally finite type morphisms. The item must prove those bounds from its different hypotheses and then transport the representative over T.

lem-sfb-big-site-open-cover-size-closure vs def-pc-fppf-site: the latter defines the site and its slice, with objects and coverings; its statement does not assert the bounded-open-cover closure theorem.

## Review by Q25

I read sets.tex section-categories-schemes, the definition of size preceding 000I, lemma-construct-category (000J), lemma-bound-affine (000P), lemma-bound-size (000Q), lemma-bound-finite-type (04T7) and lemma-what-is-in-it (000R), especially (6) and its proof. For the first new node, every hypothesis of 04T7 is copied: schemes X,S, locally finite type f, and quasi-compact X. Size is defined inline rather than delegated to a tag, and no target quasi-compactness or quasi-separatedness is introduced. For the second new node I checked 000R(6): the witness T must be an object of the chosen category, each open has size at most s(T)^aleph_0, and the cover has at most that cardinality. Topologies 021R specifies the underlying full category. The representative conclusion is a scheme isomorphism, not yet an isomorphism over an arbitrarily fixed base. That latter passage is the item's elementary final step, so no clause of the item is hidden in the prerequisite.

In step 1 I opened lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact: its clause (iii) is exactly quasi-compactness of Spec R. Carrying a cover through the affine-scheme isomorphism is elementary. I then apply the new 04T7 node to each W_j; its source hypothesis has been supplied and local finite type was given. I deliberately do not assume the preimages of affine opens under f_j are quasi-compact. In step 2 I opened lem-weil-pbc-scheme-coproduct-family: its statement supplies existence, the induced-map universal property, open coprojections, and their covering. Those are all the geometric assertions used there. Isomorphic schemes have bijective affine-open sets and isomorphic section rings, so their sizes agree. The two cardinal inequalities follow from the defining maximum and the injection into constant sequences. This two-line assembly is elementary, not a new node.

Step 3 uses the new open-cover closure node, not merely the definition of a site. Its two bounds were proved in steps 1 and 2, and T is an object of the fixed big category. I opened def-pc-fppf-site: it explicitly describes the category over S and its objects. Step 4 uses that slice definition and the full category specified in the closure node: composing the chosen isomorphism e with f defines the structure morphism, and its equality f e=f_0 proves the over-T condition. No condition about fppf coverings is applied to f_0.

For small cases I checked J empty, a singleton, infinitely many empty summands, T empty (all W_j must then be empty), a non-quasi-compact base, and a finite base with the countable bound. The empty family is accepted by the closure node without invoking the empty instance of 000Q. The finite field base has size aleph_0 even if its set of affine opens is finite; an at most countable union therefore fits the same bounds. The new size statement works for the zero ring and finite rings since its maximum always includes aleph_0; the closure statement includes arbitrary overlaps and the empty cover. No separatedness, flatness or finite presentation hypothesis was smuggled in.

Both new files have statements only, no proof sketch or proof dependencies, introduce all objects, define size inline, and record sources by tag and TeX label. Neither is elementary: the size estimate contains finite affine refinements and cardinal estimates, while the closure criterion depends on the chosen-category construction. Existing definitions and Mathlib leaves are reused for their notions. All four item steps are below 2000 characters. The dependency union equals proof_deps, no existing dependent node is cited, and citations.json copies the actual statement of every cited node. The correction during self-review was to cite the closure node's explicit full-category specification in step 4 as well, so fullness is not taken from an unstated claim in the slice definition.

## Unfinished work

No missing item argument. The two general prerequisites remain statement-only stage-1 work by design; they are not Lean proofs or Mathlib leaves.
