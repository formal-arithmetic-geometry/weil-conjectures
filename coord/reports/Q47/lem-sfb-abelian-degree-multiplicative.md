# Stage-1 report: lem-sfb-abelian-degree-multiplicative

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-abelian-degree-multiplicative.json (item, split); dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-degree-composition.json (new statement-only lemma, unsplit, no Mathlib match). citations.json contains the verbatim statements backing all thirteen step citations; searches.jsonl retains the actual search records.
2. Attachments: none. Searching WeilConjectures/ for the blueprint id, isogeny, isogenyDegree and degree/composition found the existing isogeny finite-flat/rank results, but no declaration of multiplicativity extended by zero.
3. WANTED: none. Milne AV and the cited Stacks sources are present.
4. The item has no statement error. Its kernel order is scheme length, not geometric point count. The inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor reports, and its full inherited via/place chain is retained. The current latest blueprint's direct-image argument (3), unit and chapter were read; this is an auxiliary abelian-variety input in the inherited alteration route, not a change to the unit or chapter. The two isogeny criteria already existed and were reused rather than duplicated. The item is an auxiliary lemma, not the unit's key statement, so no realized field is changed.
5. Nothing mathematical is left unfinished in the item's assembly proof. The one new input remains statement-only, as required for a one-level split.

## Review by Q47

I read Milne, Abelian Varieties, Chapter I Proposition 7.1 and the following degree paragraph on printed p.32. Proposition 7.1 identifies the equal-dimension surjectivity and finite-kernel criteria; the degree paragraph uses the full function-field degree and the rank of the finite locally free pushforward, without assuming separability. I read the two existing criterion nodes in full and checked their conclusions against each use. I also read the latest blueprint isogeny-degree statement and the current Lean Isogeny.lean rank results. Milne's convention agrees with the order of the scheme-theoretic kernel through lem-sc-isogeny-degree, not through counting points.

Step 1 uses exactly def-sc-group-scheme's kernel fibre-product and finite-order definitions, and def-sc-isogeny's criterion. The identity kernel is Spec k and its coordinate algebra has dimension one; the argument proves the identity clause directly.

Step 2 uses def-sc-isogeny to obtain surjectivity and finiteness of the composite kernel. The statement of lem-sfb-equal-dimension-isogeny-criterion applies to a:A→A because the dimensions agree tautologically and it is a group homomorphism. For b I wrote out the inclusion of kernel schemes and the quotient-of-a-finite-algebra argument; this retains nilpotents and proves actual scheme finiteness. lem-sc-kernel-subgroup supplies closed subgroup kernels, and def-sc-group-scheme supplies the fibre-product and functor-of-points interpretation, so this argument does not use only an inclusion of geometric point sets. The statement of lem-sfb-finite-kernel-equal-dimension-isogeny explicitly allows the given algebraically closed field and implies surjectivity from the finite scheme-theoretic kernel and equal dimensions. Its conclusion plus the finite kernel is precisely the definition of an isogeny. None of these dependencies reaches this item: the server DAG check is requested below as an additional cycle check.

Step 3 first applies the already-read surjectivity criterion to the composite, after checking that both factors are surjective on scheme points. lem-sc-isogeny-degree explicitly supplies finite flatness and constant pushforward rank equal to kernel order for all three isogenies. I corrected an implicit finite-presentation inference in my first draft: step 3 now explicitly applies lem-sfb-finite-kernel-equal-dimension-isogeny to a, b and the composite, using their finite kernels and equal dimensions. Its statement directly supplies finite local freeness, so no additional theorem about finite presentation is assumed. The new general composition-degree lemma then supplies only the multiplication of ranks, not the abelian-variety criterion or the zero cases. I compare the two constant degrees at the identity point, avoiding a rank uniqueness claim on an empty base.

Step 4 is the contrapositive of step 2 and the zero-extension definition. Thus the proof covers a nonisogeny on either side, including the asymmetric case in which a is an isogeny but b is not. No non-elementary result is hidden in this step.

For the new node I read Stacks morphisms.tex: Tags 02KA (definition-finite-locally-free), 02KB (lemma-finite-flat) and 02KC (lemma-composition-finite-locally-free), and algebra.tex Tag 02M9 (lemma-locally-free-semi-local-free). The last result is needed to justify the constant-degree refinement of 02KC, whose printed statement only gives composition permanence. Here is the proof material retained for its future worker: for a point z of S, put K=κ(z), B=Γ(Y_z,O) and C=Γ(X_z,O). Base change gives dim_K B=s and a finite locally free B-algebra C of constant B-rank r. The finite-dimensional K-algebra B is Artinian and semilocal; if B is nonzero, 02M9 makes C free of rank r over B. A B-basis of C and a K-basis of B give a K-basis of C indexed by their product, hence dim_K C=rs. If B=0 then C=0 and the same formula holds. Composition is finite locally free by 02KC. This is a real intermediate lemma about arbitrary schemes, not a restatement of any clause about abelian endomorphisms. This argument belongs here in the report, not in the unsplit node.

I checked the Mathlib search hits themselves. FlatRank.finrank_comp_left_of_isIso assumes an isomorphism and cannot multiply two arbitrary ranks. Module.finrank_mul_finrank assumes globally free scalar towers; a fibre-algebra/semilocal reduction is required to use it here, so the new scheme statement is not a one-line Mathlib specialization. Semantic searches also returned finite composition instances, which omit the degree formula. Both phrasings, Loogle, grep and LeanSearch are recorded exactly as run. No unavailable service was declared a negative result.

Small cases: identity and automorphisms have kernel order one. For a positive-dimensional A the zero endomorphism has kernel A and degree zero; products involving it satisfy the zero case. Projections on E×E and their composites are covered by step 2, with no false assumption that a surjective composite alone forces b surjective for arbitrary maps. In characteristic p an inseparable isogeny is counted by its nonreduced kernel algebra, e.g. Frobenius, so the rank calculation retains the inseparable factor. The new lemma allows r=0, s=0, empty schemes and nonreduced Artinian fibre rings; if S is empty its degree assertion is vacuous. No step exceeds 2000 characters, no new node is elementary, and the new statement has no proof or proof dependencies. Existing nodes were searched across the whole DAG and blueprint before creation. The generic tools from the abelian-variety chapter are declared in split_report.tool_uses; the two same-unit criteria preserve the inherited route.

## Not duplicates

lem-sfb-finite-locally-free-degree-composition vs lem-trf-finite-locally-free-composition: the existing Mathlib leaf proves permanence only; the new lemma adds multiplication of prescribed constant fibre degrees, including rank zero.

lem-sfb-finite-locally-free-degree-composition vs lem-coef-relative-undercategory-limit-creation: the source-tag text belongs to a categorical reference; its statement concerns quasicategory undercategories, not scheme ranks.

lem-sfb-finite-locally-free-degree-composition vs lem-a1-affine-relation-comparison-preparation: the existing statement concerns groupoid and comparison data for an affine finite flat relation; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-a1-finite-locally-free-principal-basis-cover: the existing statement concerns principal fixed-rank bases for a finite locally free affine algebra; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-a1-local-trivialization-residue-rank: the existing result computes a module residue dimension from a local trivialization; it does not multiply two morphism degrees.

lem-sfb-finite-locally-free-degree-composition vs lem-a1-semilocal-submodule-basis: the existing result selects a basis from a spanning submodule with infinite residue field; the new result is composition of scheme degrees and has no residue-field infinitude assumption.

lem-sfb-finite-locally-free-degree-composition vs lem-a1-basis-of-maximal-residue-bases: the existing result tests a specified module basis using all maximal residue fields; it does not assert the degree of a composite morphism.

lem-sfb-finite-locally-free-degree-composition vs lem-pc-finite-affine-fibre-sections: the existing statement concerns affine calculation of fibres of a finite pushforward; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-sc-finite-pushforward-rank-on-open: the existing statement concerns rank of finite flat pushforward on a constant-rank open; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-sc-finite-pushforward-locally-free: the existing statement concerns pushforward of a finite flat morphism is locally free of locally constant rank; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-pc-cartier-criterion: the existing statement concerns the cartier criterion on smooth one-dimensional fibres; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-sfb-constant-hilbert-finite-locally-free: the existing statement concerns constant projective hilbert polynomial characterizes finite locally free families; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-sfb-etale-groupoid-affine-stabilizer-splitting: the existing statement concerns affine etale splitting of a scheme groupoid at a finite stabilizer; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-sfb-finite-kernel-equal-dimension-isogeny: the existing result is a finite-kernel/surjectivity criterion for abelian varieties; the new result multiplies degrees of two given finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-weil-pbc-finite-free-algebra-spectrum: the existing statement concerns the spectrum of a finite free algebra is finite locally free; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-weil-pbc-finite-locally-free-degree-etale-descent: the existing statement concerns finite locally free of degree d descends along etale coverings (stacks 02vo); it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.

lem-sfb-finite-locally-free-degree-composition vs lem-weil-pbc-finite-locally-free-degree-locally-constant: the existing statement concerns the fibre degree of a finite locally free morphism is locally constant; it does not give the product of prescribed constant degrees for two arbitrary finite locally free morphisms.
