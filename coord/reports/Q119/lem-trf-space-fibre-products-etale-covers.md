## Worker report

Files written: the repaired item and three new statement-only nodes, all in dag/nodes/sec-trace-formula/.

- lem-trf-sheaf-pullback-diagonal: statement; unsplit; no Mathlib match.
- lem-trf-fibre-product-atlas-tests: statement; unsplit; no Mathlib match.
- lem-trf-presheaf-pullback-etale-point-lifting: statement; unsplit; no Mathlib match.

Attachments: none. The upstream WeilConjectures source search by blueprint tag and AlgebraicSpace gives no declaration; all three declarations in Sheaf/AlgebraicGeometry/AlgebraicSpaceFibreProductsEtaleCovers.lean end in sorry.

WANTED: none.

The return requests spreading the 4108-character argument over at least two comparable statement-only tasks. This repair creates three: old steps 1+2+5, 3+4, and 6+7. No argument is discarded. The item statement is unchanged; its proof is now a short assembly. The sandbox initially contained only dispatcher markers, so the current read-only repository node is the repair base. Its existing searches, source, ancestry, Lean records and prior metadata are retained.

Nothing is left unfinished within this stage-1 item. Proving the three children belongs to subsequent workers; they deliberately have empty proof/proof_deps and null proof_origin. No Lean was written or compiled.

## Review by Q119

I read spaces.tex, lemma-fibre-product-spaces-over-sheaf-with-representable-diagonal (04T9) and lemma-fibre-product-spaces (02X2), spaces-topologies.tex lemma-etale (041F)(3), and spaces-properties.tex definition-points (03BU), its preceding presheaf point relation, and lemma-points-cartesian (03H4) with its proof. These support the same sheaf construction as the returned proof. The new equality-locus statement requires only the diagonals of F and G; H need only be a sheaf. The new atlas statement requires the diagonal of H, not an atlas of H or diagonals of F and G. It explicitly fixes both atlases and gives their test-scheme models. The third task makes the two different tests explicit: scheme tests for representable etaleness and field-extension tests for joint surjectivity. It assumes representable etale maps, preserving the item's convention rather than silently switching to chartwise etale maps.

Parent step 1 cites the first child's sheaf and equality-locus conclusions and the algebraic-space definition for its hypotheses. Step 2 cites the definition for existence of U,V and the diagonal of H, and the second child's scheme atlas and representable-surjective-etale conclusions. All three defining conditions are then literally present. Step 3 uses the first child's Hom-bijection and the definition's explicit statement that morphisms are natural transformations; restricting that bijection to algebraic-space test objects is elementary. Step 4 first uses the construction already assembled, then cites precisely the third child's scheme-test and field-lifting conclusions. Every uses entry is backed by its actual statement in citations.json; no proof internals or definition-only theorem citations are used.

Small cases: if a sheaf is empty the compatible-pair construction and equality loci are empty where appropriate. If F,G,H are representable the equality-locus and atlas tests reduce to ordinary scheme fibre products. Identity atlases give the ordinary identity test; arbitrary U,V need not be affine, separated or quasi-compact. For the third task, no map on point sets is assumed injective and no representative need lift over its original field: extensions are allowed. An empty index set forces no H field representatives, hence none for G, so its conclusion is valid. No nonempty-base assumption or hidden finite-type hypothesis is used.

For B1-B7 I checked that every new statement introduces S, sheaves, maps and tests, cites the definitions of its notions, contains only the claimed constructions/properties and no proof sketch, and has a tag and the actual TeX label. All three tasks are unsplit, with no proof dependencies, and no source is SGA. DAG searches included tags 04T9,02X2,041F,03BU,03H4, representable diagonal, sheaf fibre product, equality loci, atlas, common extensions and field-valued pullbacks; blueprint_refs searches included representable diagonal, equality locus, atlas, fibre product, etale cover and field extension, and ancestor was checked. The chartwise permanence node depends on this item, so using it would be circular and would change the convention. The scheme-point lemma has only scheme C,U and algebraic-space E and does not state the sheaf-test identification or the family lifting task.

The new nodes have two distinct LeanFinder phrasings each, a Loogle query, a Mathlib grep and an unavailable LeanSearch entry, all executed with msearch.py and recorded verbatim. I read the results: scheme pullback permanence and scheme carrier lemmas do not cover sheaf presentations. I also opened CategoryTheory/MorphismProperty/Representable.lean, especially of_diag, diag_of_map_from_obj, diag_iff and the pullback3 identities: these are useful tools but do not state the first task's sheaf condition, simultaneous equality-locus model and Hom-bijection in one specialization. The new statements are therefore not Mathlib leaves. No new proof step exceeds 2000 characters; the whole parent assembly is below 3000.

## Repair of the return

The sole numbered requirement was re-splitting for parallel work. All seven arguments are assigned explicitly below and preserved verbatim, including the original scheme permanence citations. Three balanced tasks replace the long proof; none states algebraic-space closure plus covering preservation, and none receives the whole item. The elementary-node restriction is read with the explicit human requirement to distribute this returned argument: the children group coherent constructions rather than isolate one-line consequences. The old universal property argument is in the first child's statement; only its full-subcategory assembly remains in the parent.

## Not duplicates

- lem-trf-sheaf-pullback-diagonal vs lem-trf-space-fibre-products-etale-covers: only the sheaf/diagonal/Hom construction, without any atlas or covering claim.
- lem-trf-fibre-product-atlas-tests vs lem-trf-space-fibre-products-etale-covers: only the explicit atlas and test-scheme construction, without the diagonal, universal property or covering assertion.
- lem-trf-presheaf-pullback-etale-point-lifting vs lem-a1-space-affine-etale-cover: the existing node constructs affine atlas refinements and a topology; this task gives pullback test schemes and field-extension lifts for a specified family.
- lem-trf-presheaf-pullback-etale-point-lifting vs def-a1-algebraic-space-point-classes: the existing node defines point classes; this task proves scheme-test identifications and lifting properties.
- lem-trf-presheaf-pullback-etale-point-lifting vs lem-a1-space-etale-open-image: the existing node concerns open images and quasi-compactness of algebraic spaces and cites this parent; this task concerns sheaf test objects and representative lifts without topology.
- lem-trf-presheaf-pullback-etale-point-lifting vs lem-a1-space-fibre-product-point: the existing node assumes C,U schemes and E an algebraic space and supplies a point; this task concerns arbitrary sheaves, representable-etale scheme tests and the full extension-lifting assertion for families.
- lem-trf-presheaf-pullback-etale-point-lifting vs def-a1-space-point-topology: the existing node defines a topology; this task neither defines nor uses a topology.
- lem-trf-presheaf-pullback-etale-point-lifting vs lem-zl-generic-fiber-components-section: the existing node concerns generic-fibre profinite component sections and derived topoi, not any of these sheaf constructions.
- lem-trf-presheaf-pullback-etale-point-lifting vs def-trf-algebraic-space-jointly-surjective-family: the existing node defines joint surjectivity; this task proves scheme-test identifications and gives explicit extension lifts for the pulled-back family.
- lem-trf-presheaf-pullback-etale-point-lifting vs lem-trf-space-fibre-products-etale-covers: the scheme-test and field-representative mechanism for sheaves, without asserting algebraic-space closure or categorical fibre products.
- lem-trf-presheaf-pullback-etale-point-lifting vs lem-trf-space-chartwise-etale-permanence: the existing node uses chartwise etaleness of algebraic spaces and depends on this parent; this task is the explicit sheaf scheme-test and representative-lifting mechanism in the representable convention.

## Preserved argument assignments for subsequent workers

### Old step 1 assigned to lem-trf-sheaf-pullback-diagonal

Put $P(T)=\{(x,y)\in F(T)\times G(T):f(x)=g(y)\text{ in }H(T)\}$, with componentwise restrictions. This is a sheaf: a matching family of pairs glues uniquely in $F$ and $G$; the images of the two glued sections in $H(T)$ agree because their restrictions agree on the covering and $H$ is a sheaf. This uses the sheaf equalizer condition in [def-weil-pbc-sites-and-cohomology] and the sheaf part of [def-trf-algebraic-space]. Thus $P$ is the sheaf fibre product.

Uses: def-trf-algebraic-space, def-weil-pbc-sites-and-cohomology.

Source: literature/stacks-project/spaces.tex; Tag 04T9, first paragraph of proof: the sheaf condition, expanded using the sheaf equalizer definition.

### Old step 2 assigned to lem-trf-sheaf-pullback-diagonal

To test the diagonal of $P$, take a scheme $T$ and two sections $(x_1,y_1),(x_2,y_2)\in P(T)$. The equality locus $A=T\times_{(x_1,x_2),F\times F,\Delta_F}F$ is a scheme, and likewise $B=T\times_{(y_1,y_2),G\times G,\Delta_G}G$, by representability of the two diagonals. For every scheme $Z\to T$, a section of $A\times_TB$ is precisely simultaneous equality of the two $F$ sections and the two $G$ sections, hence equality of the two $P$ sections. Consequently $A\times_TB$ represents the pullback of $\Delta_P$ to $T$. This scheme exists by [def-pc-fibre-product], so $\Delta_P$ is representable.

Uses: def-trf-algebraic-space, def-pc-fibre-product.

Source: literature/stacks-project/spaces.tex; Tag 04T9, diagonal cartesian square, with representability checked directly on a scheme test.

### Old step 3 assigned to lem-trf-fibre-product-atlas-tests

Choose the representable surjective etale atlases $U\to F$ and $V\to G$ supplied by [def-trf-algebraic-space]. The sheaf $W=U\times_HV$ is a scheme: it is the pullback of $\Delta_H:H\to H\times H$ along the map $U\times_SV\to H\times H$ induced by $U\to H$ and $V\to H$. The source of this test is a scheme by [def-pc-fibre-product], and the diagonal of the algebraic space $H$ is representable. The maps to $F$ and $G$ induce $W\to P$.

Uses: def-trf-algebraic-space, def-pc-fibre-product.

Source: literature/stacks-project/spaces.tex; Tag 04T9, last paragraph: the scheme atlas U times_H V.

### Old step 4 assigned to lem-trf-fibre-product-atlas-tests

For a scheme $T\to P$ with components $x:T\to F$, $y:T\to G$, form the schemes $A=T\times_FU$ and $B=T\times_GV$. Their maps to $T$ are surjective etale by the atlas definition. The pullback $T\times_PW$ is represented by $A\times_TB$: on every test scheme its data are exactly the two lifts of $x,y$, whose images in $H$ already agree. The projection $A\times_TB\to B$ is surjective and etale by [lem-weil-pbc-surjective-base-change] and [lem-weil-pbc-etale-scheme-base-change]. Composing with $B\to T$ preserves surjectivity by [lem-trf-surjective-morphism-composition] and etaleness by [lem-weil-pbc-etale-composition-cancellation](2). Thus $W\to P$ is representable surjective etale. Together with steps 1 and 2 this verifies all three algebraic-space conditions and proves that $P$ is an algebraic space.

Uses: def-trf-algebraic-space, def-pc-fibre-product, lem-weil-pbc-surjective-base-change, lem-weil-pbc-etale-scheme-base-change, lem-trf-surjective-morphism-composition, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/spaces.tex; Tag 04T9, last paragraph; the atlas tested on schemes, with scheme permanence from Tags 01S1, 02GO and 02GN.

### Old step 5 assigned to lem-trf-sheaf-pullback-diagonal

For any algebraic space $Q$, a morphism $Q\to P$ sends a section $q$ to a compatible pair of sections in $F$ and $G$. Conversely a pair of natural transformations $Q\to F$, $Q\to G$ whose composites to $H$ agree defines $q\mapsto(a(q),b(q))$ in $P$, naturally in the test scheme. These constructions are inverse. Since morphisms of algebraic spaces are natural transformations [def-trf-algebraic-space], this is exactly the required categorical universal property.

Uses: def-trf-algebraic-space.

Source: literature/stacks-project/spaces.tex; Tag 02X2, universal property in the full subcategory, written on sections.

### Old step 6 assigned to lem-trf-presheaf-pullback-etale-point-lifting

Apply the fibre-product construction just proved to $G\to H$ and $H_i\to H$, so $P_i=G\times_HH_i$ is an algebraic space. For every scheme $T\to G$, the pullback $T\times_GP_i$ is $T\times_HH_i$: both functors consist of a section of $T$ and a compatible section of $H_i$. Since $H_i\to H$ is representable etale in the convention of the statement, this is a scheme etale over $T$. Thus each $P_i\to G$ is representable etale by [def-trf-algebraic-space]. In particular, taking $T=G$ when $G$ is a scheme shows that $P_i$ is a scheme, as required.

Uses: def-trf-algebraic-space.

Source: literature/stacks-project/spaces-topologies.tex; Tag 041F(3), etaleness and scheme special case proved directly by the scheme-test definition.

### Old step 7 assigned to lem-trf-presheaf-pullback-etale-point-lifting

It remains to prove joint surjectivity, without invoking the omitted proof of Tag 041F(3). Let $z\in|G|$ be represented by $a:\operatorname{Spec}K\to G$. Joint surjectivity of the given family gives $i$ and a representative $b:\operatorname{Spec}L\to H_i$ whose image in $|H|$ is the image of $z$. By the point equivalence relation stated above, there is a common extension $M$ of $K$ and $L$ on which the two maps to $H$ agree. The pair $(a|_M,b|_M)$ is therefore a section of the sheaf $G\times_HH_i$ over $\operatorname{Spec}M$, and its point maps to $z$ because $a|_M$ is equivalent to $a$. This proves that every point is covered. If $I$ is empty, the hypothesis gives $|H|=\varnothing$ and any point of $G$ would map to a point of $H$, so $|G|=\varnothing$ and the conclusion still holds.

Uses: def-trf-algebraic-space, def-weil-field.

Source: literature/stacks-project/spaces-properties.tex; Tag 03BU (definition-points) and Tag 03H4 (lemma-points-cartesian), common-field-extension argument; supplies the joint-surjectivity detail omitted at spaces-topologies.tex Tag 041F(3).

