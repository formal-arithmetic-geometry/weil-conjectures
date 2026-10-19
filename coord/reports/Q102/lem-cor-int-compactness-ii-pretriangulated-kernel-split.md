1. Files written

- `dag/nodes/sec-six-functors-basics/lem-cor-int-compactness-ii-pretriangulated-kernel-split.json`: split item, four complete steps. Statement, statement dependencies, source, original provenance and earlier Mathlib searches retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-pretriangulated-monomorphisms-split.json`: one new Mathlib leaf, exact `CategoryTheory.Pretriangulated.instSplitMonoCategory`, `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:466–472`.
- `citations.json`: verbatim quotes for every node cited by every proof step.

2. Attachments: none. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, kernel preservation, projection/coprojection normal forms and splitting monomorphisms found no project declaration stating the whole item. Mathlib components are used as leaves, rather than claimed as project attachments.

3. WANTED: none.

4. Problems corrected: the imported statement is correct; no hypotheses or conclusion were changed. The first dry run caught searches recorded under sibling item directories. New searches now use the assigned item, with exact tool/query texts and raw msearch.py log records. The next dry run rejected deferring the whole normal form as the only non-elementary dependency. I removed that uncommitted proposal and wrote the decomposition argument into the item. The only new dependency now says merely that monomorphisms split, an exact Mathlib fact used twice. Proposed auxiliary leaves for elementary biproduct calculations were also removed before delivery. Composition order and the arbitrary target-object quantifier are explicit in the final argument. Original protected item metadata and historical search entries have been restored unchanged.

5. Nothing remains unfinished. The new leaf has no proof or proof dependencies; the item's proof supplies the cone, its splitting, the induced monomorphism, and every image-kernel factorization.

## Not duplicates

lem-sfb-pretriangulated-monomorphisms-split vs lem-cor-int-compactness-ii-pretriangulated-kernel-split: the new leaf gives a retraction of a monomorphism in one category; the item concerns preservation of arbitrary existing kernels by an additive functor to a merely preadditive target. The complementary map and its monicity, and the entire image-kernel universal property, are proved in the item.

lem-sfb-pretriangulated-monomorphisms-split vs lem-pc-derived-zero-third-split: the existing node gives a compatible biproduct isomorphism for a supplied distinguished triangle with zero third arrow; the new leaf gives a retraction of any monomorphism without supplying a triangle or assuming its third arrow is zero. Both are used at their actual scope.

I searched the entire DAG for the new id, instSplitMonoCategory, SplitMonoCategory, monomorphism/retraction/splitting terminology and kernel normal forms, and searched the entire blueprint with blueprint_refs.py for the tag and these concepts. No node already states this monomorphism-retraction result. Keyword hits in other nodes' search histories do not assert it. The new leaf has no Stacks tag shared with an existing source. Its nearest blueprint ancestor is det-cor-int-compactness-ii-extension-zero, with the assigned item in its via list. same_as is empty.

## Review by Q102

I read the chapter, current unit, current main-20261015 ancestor proof (1), the reviewed parent's Step 2, and Stacks `literature/stacks-project/derived.tex`, Tag 05QU (`lemma-when-split`), statement and full proof. I read the preceding splitting lemma and Tags 0146 and 0149 in the same source. The final proof follows 05QU's two successive monomorphism splittings, and writes out how the resulting identities imply preservation by any additive functor. It requires only a pre-triangulated category, not the octahedral axiom, idempotent completeness or arbitrary existing kernels. This auxiliary node does not realize the unit's key statement, so no unit realization record is changed. No coefficient comparison or base-change morphism occurs and no SGA source is used.

For the new leaf I read `Pretriangulated.lean:466–472` and `CategoryTheory/EpiMono.lean:50–54,170–172`. The former is exactly the SplitMonoCategory instance, whose definition gives a retraction to every monomorphism. The node explicitly defines monomorphism by cancellation. LeanFinder, LeanSearch, Loogle and grep actually ran; their unchanged tool/query texts, raw records and assessed matches are recorded. No unsplit non-Mathlib node is created.

Step 1 uses only the unique-factorization clause in the item's definition of kernel: two maps into K with equal composites with k are two factorizations of one annihilated map, hence equal. This checks monicity without importing an extra kernel lemma.

For Step 2 I reopened every cited statement: def-weil-triangulated-category gives cone completion, rotation, additive shift and its identity/composition laws; the new Mathlib leaf gives r_0 k=1; clause (i) of lem-weil-pbc-hom-into-triangle-exact gives the zero composite in the twice-rotated triangle; lem-pc-derived-zero-third-split gives the isomorphism e with both specified compatibility equations; def-weil-additive-category gives exactly the biproduct identities used to derive rk=1, pk=0, ps=1 and kr+sp=1. Thus the triangle's third arrow is proved zero before the splitting lemma is applied. Signs in the twice rotation are harmless because (-k[1])h=0 implies k[1]h=0, and applying r_0[1] gives h=0.

Step 3 proves d=gp by multiplying the decomposition identity by d, proves g monic using the given kernel's factorization and ps=1, pk=0, and only then applies the new leaf again to get t with tg=1. The use of subtraction is covered by the cited preadditive-category definition; every object and map is already introduced. No normal-form or restricted-map lemma is silently quoted.

Step 4 cites only def-weil-pbc-additive-functor and def-weil-preadditive-category, whose statements give preservation of the Hom-group operations and bilinear composition. Functoriality and those definitions carry the established identities through F. For an arbitrary object T of the target and a killed by F(d), the displayed equations give F(p)a=0 and the factorization b=F(r)a. Applying F(r) gives uniqueness. F(d)F(k)=0 is checked separately. T is not assumed in the image of F; the target is not assumed additive, complete or equipped with kernels.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these final files: all citations have verbatim statement quotes; every non-elementary ingredient is a cited node; every use matches its actual hypotheses; no definition is substituted for a theorem; no new node restates a clause of the item. All proof steps are below 2000 characters. I tested d=0 (k is an isomorphism), d=1 (K=0), a split inclusion, the zero functor, and the zero category. In each case the equations give the expected universal property. The argument still treats only an existing kernel when other kernels fail to exist. No false statement or source error was found.
