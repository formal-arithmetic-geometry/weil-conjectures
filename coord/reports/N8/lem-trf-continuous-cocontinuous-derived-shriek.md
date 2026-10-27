# N8: returned-head stage-1 re-split

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-continuous-cocontinuous-derived-shriek.json`: statement unchanged; five-step assembly, 2965 characters.
- `dag/nodes/sec-trace-formula/lem-trf-ringed-site-restriction-generator-data.json`: statement, unsplit; no Mathlib match for the full exact-restriction and varying-ring free-sheaf presentation/representation result.
- `dag/nodes/sec-trace-formula/lem-trf-ext-orthogonal-adjoint-acyclic.json`: statement, unsplit; no Mathlib match for the Ext-family criterion transferring acyclicity across a possibly nonexact adjoint.
- `dag/nodes/sec-trace-formula/lem-trf-additive-homotopy-triangulated.json`: statement, Mathlib leaf; `HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory`, `Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:596` (instance body through line 601).
- `citations.json`: every citation in the five assembly steps has a verbatim statement quote.
- `searches.jsonl`: actual msearch results; the original queries, result digests and availability are preserved.
- `report.md`: this report, including the complete returned proof and its extraction map.

## Attachments

None. I searched the current read-only `lean/WeilConjectures/` both for the blueprint tag and for continuous/cocontinuous derived lower-shriek and generator/acyclicity concepts. The exact full item has no finished upstream declaration. Its local `Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek` statement is not an upstream finished proof. The free-Yoneda lifting statements in `WeilConjectures/ConstructibleSheaf/FreeLifting.lean` concern constant coefficients on scheme etale sites, not all varying ring sheaves on small sites. The original `lean` and audit metadata are retained for the maintainer.

## WANTED

None. All mathematical sources used are in the literature directory.

## What was wrong and what changed

This repairs the 2026-10-22 re-split return at `adf3670da5fa81b4b128e91507bbaa06a17513de`. The sandbox initially contained only dispatcher markers, with no item, report, citations or search log to reuse. I recovered the eight-step returned split from the current shared read-only node, which retains exactly the eight steps and lengths in the return. I preserved its statement, source, old searches, blueprint ancestry and existing metadata. The delivery tool overlays the repaired stage-1 fields onto its freshly fetched main branch; no git command was run in the read clone.

The first new work item carries the exactness/local-lifting argument and the free-sheaf presentation and representation arguments. It does not assert the existence of the ordinary or derived left adjoint: assembly step 1 still applies the existing partial-adjoint criterion and proves additivity and colimit preservation. The second new work item carries the independent Hom-complex and injective-detection argument, abstracted to any additive adjunction from a ringed module site. It does not assert existence of a derived functor. Both are genuinely smaller arguments and are left statement-only, with empty proof/proof_deps and null proof_origin. They are of comparable proof size: the first collects old steps 1 and 2 and the first half of 3 (about 2000 characters of argument); the second takes old step 5 (1149 characters). The third extracted argument is already Mathlib, so it is delivered as a leaf rather than as an unnecessary open task.

No statement dispute was found. No target, unit, coefficient category, definition or route changes were made. The item remains the generic lower-shriek input in the recorded derived-colimit/bar ancestry of `lem-trf-local-term-locality`; the zero-stalk curve unit and its chapter are unchanged. No prohibited SGA source is used.

## Extraction map and handoff arguments

Every argument of the returned proof is accounted for below. The full original proof follows verbatim at the end, so no worker has to reconstruct the details from a summary.

1. Old step 1, exactness of restriction, moves to `lem-trf-ringed-site-restriction-generator-data`. Its worker uses `def-weil-sheaf-of-modules-category` for kernels and sheafified cokernels and `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective` for local lifts. The underlying abelian-sheaf cokernel equals the module cokernel on underlying sheaves. Thus cocontinuity refines each cover on which a section lifts, giving preservation of epimorphisms; restriction already preserves kernels sectionwise. The identity coefficient map makes module pullback literal restriction.
2. Old step 2 and the representer computation in old step 3 move to the same new node. Its worker has `lem-weil-pbc-free-yoneda-presheaf-module` and `def-weil-presheaf-modules-sheafification` for the evaluation adjunction, `lem-pc-sites-modules-quotient-j-shriek` for the epimorphic presentation, and the small-site Grothendieck theorem for coproduct existence. For varying ring sheaves these are the sheafifications of free presheaf modules on each representable, not just copies of a global unit. A map from a coproduct is a tuple of maps; the evaluation at uU is therefore represented by the corresponding coproduct on the other site. The smallness of objects and sections ensures the sum is genuinely small. Empty sums give zero; concatenating finite collections of small indexing sets proves finite-sum closure.
3. The remainder of old step 3 stays in assembly step 1. The new node supplies exactly the hypotheses of `lem-trf-partially-defined-module-adjoint`, with its categories reversed relative to the naming there. Natural Hom bijections and additivity of restriction show that the resulting left adjoint preserves sums of maps. `lem-weil-pbc-left-adjoint-preserves-colimits` gives right exactness and sequential-colimit preservation. Its value on E_U is determined by the same natural representing bijections.
4. Old step 4 stays in assembly step 2, citing the existing `lem-trf-module-pullback-injective-section-acyclic`. This is specifically module-injective acyclicity, not the abelian-sheaf-only special case, and its E_U is literally the new node's sheafification.
5. Old step 5 moves to `lem-trf-ext-orthogonal-adjoint-acyclic`. Its worker uses the existing `lem-trf-acyclic-coproduct-ext-orthogonal-hom` with F=TJ. The ordinary adjunction is an additive bijection in each degree and natural in the first variable; it therefore respects precomposition with every differential and the sign (-1)^(n+1). To detect acyclicity, a nonzero H^r embeds into an injective J. Extend this nonzero map from Z^r/im(d^(r-1)) to B^r/im(d^(r-1)) by injectivity; the induced B^r to J is a Hom cocycle nonzero on cycles. A Hom boundary factors through d^r and is zero on cycles. This contradiction proves acyclicity of the image complex. No injectivity of TJ is used. This is a separate argument beyond the source-Hom lemma, not a new name for that existing lemma.
6. Old step 6 stays in assembly step 3. All five hypotheses are visible there: class properties, preservation of bounded-above acyclic class-complexes, existence of sequential colimits in both categories, their exactness, and preservation by the left adjoint. The `lem-trf-unbounded-left-derived-criterion` conclusion is precisely denominator-pro-system definedness everywhere, and `new-everywhere-defined-derived-functors` is the separate assembly theorem supplying the universal comparison.
7. The cone/homotopy argument in old step 7 is now `lem-trf-additive-homotopy-triangulated`, the Mathlib leaf. I read its anonymous instance at lines 596-601 and its `mappingCone.mapTrianglehIso` at lines 455ff. It supplies the shift-compatible cone-triangle functor, not exactness of the ordinary additive functor. The remaining part of step 7 stays in assembly step 4: exact localization, saturation/triangulation compatibility, everywhere-definedness, and the exactness theorem for the left derived functor.
8. Old step 8 remains in assembly step 5 in full; only its reference to old step 6 becomes new step 3. In particular the identity denominator, common-stage condition, representing cocone with identity leg, functorial pre-derived Hom bijection, and its specialization s=t=1 are all present, with the transpose formula in exactly the item's required direction.

## Mathlib search review

All searches for new nodes ran through the required msearch command and their raw outputs were read. For the generator node I tried both free-sheaf generator language and free-Yoneda/corepresentation language, read `Presheaf/Generator.lean` (evaluation, separating family, canonical sum), `Presheaf/Pullback.lean:70-78` (partial representer on presheaves), and the sheaf free/generators results. These give useful ingredients; none is the combined varying-ring sheaf restriction theorem. `SheafOfModules.GeneratingSections.epi` only applies after supplying generating sections of the relevant free-global-unit form. It is not the presentation indexed by all site objects used here.

For the acyclicity-transfer node I tried both Hom-complex/injective-test language and Ext-orthogonal-family adjunction language. The returned injective-dimension, derived-functor-on-injectives, and K-injective orthogonality results were read; `HomotopyCategory/KInjective.lean` explicitly concerns maps into K-injective complexes. None states that a possibly nonexact left adjoint preserves these bounded-above acyclic sums under Ext vanishing for its right adjoint. The separate injective-detection argument remains work in the new node.

For additive homotopy triangulatedness, LeanFinder, Loogle, LeanSearch and the source grep agree. The local source has an anonymous instance; the search services identify its full generated name. The grep is recorded against the directory as well as against the file, because rg omits filenames for a single file, and msearch's display then parses the line field awkwardly. The directory query gives the actual filename and line 596. The sheaf categories in this application are abelian, so the source's zero-object and biproduct hypotheses are automatic. No compiler was invoked to inspect the instance name.

The item's previous searches remain exactly as inherited; three additional real searches rechecked the possible abstract Mathlib match. `totalLeftDerived` assumes derived-functor existence and does not prove it here. The site sheaf adjunction hits do not supply the unbounded module derivability hypotheses.

## Review by N8

I read Stacks `sites-cohomology.tex`, `lemma-existence-derived-lower-shriek` (07AC) through its Ext/Hom argument, and `lemma-pullback-injective-pre-limp` (0D6X). I read `sites-modules.tex`, `lemma-lower-shriek-modules` (0797) and `lemma-module-quotient-flat` (03EW), including the explicit (U,s)-indexed presentation. For the leaf and assembly I read `derived.tex`, `lemma-additive-exact-homotopy-category` (014X), `proposition-left-derived-exists` (0794) and `lemma-derived-adjoint-functors` (09T5), and read the complete stated pre-derived canonical formula in `lem-pc-pre-derived-adjoint-functors-general`. The original item source's 0DVC/0FND normalization is retained, rather than replaced by an arbitrary existence of an adjunction.

For new assembly step 1 I opened the new restriction-generator statement, the partial-adjoint statement and the colimit-preservation statement. They supply respectively exact additive restriction with the specified generating class/representers, extension of a partial left adjoint, and preservation of every existing small colimit. The argument does not take representer functoriality from the proof of a node: naturality is explicitly in the new statement. Additivity of g_! is proved in the assembly, and the zero/finite-sum hypotheses are expressly in the new statement.

For step 2 I checked the actual module-pullback-injective statement gives Ext^p(E_U,g^-1 I)=0, not just section acyclicity for an abelian-sheaf injective. I checked the ringed-site Grothendieck statement and the enough-injectives theorem give the target hypothesis of the transfer node. In the transfer statement the small family is indexed by the small set of site objects; the complex is bounded above and each term is a small sum with repetitions. The target category is abelian and has enough injectives, while the source is the exact module-sheaf category required by its Ext-Hom input. Thus every hypothesis is supplied before the transfer theorem is applied.

For step 3 I compared all five conditions against the full statement of `lem-trf-unbounded-left-derived-criterion`, and checked that `prop-pur-kinjective-resolutions-exist` actually asserts the Grothendieck property, all colimits and exact filtered colimits. N is small filtered. No bounded-below restriction or assumption of projectives is introduced. The assembly node really asserts universal comparison transformations, so the comparison in the parent is the derived one.

For step 4 I checked the Mathlib instance is about all additive functors on homotopy categories, not just exact additive functors on derived categories. The homotopy-triangulation statement includes exactness of Q. The saturation statement includes Situation 05S8, and the left-derived-exactness statement assumes precisely definedness everywhere, already established in step 3.

For step 5 I checked the exact-functor factorization statement includes preservation of quasi-isomorphisms and the termwise derived identification. The ind-diagram definition asks for both a split leg and a common later stage: the identity denominator gives the first and filteredness gives the latter, since all transitions are isomorphisms. The full pre-derived-adjunction node gives a functorial bijection and its formula for every pair of denominators. Substituting identity denominators and f^flat makes that formula e(Q(f^flat))=Q(f) epsilon_C, so its inverse has exactly the required normalization. No assertion that pullbacks of injectives are injective is used.

I tested the new statements on the empty site/zero module categories, empty indexing families, the zero ring, the identity functor, and one-object trivial sites with an ordinary ring. All give the expected zero or usual free-module formulas. For the transfer node an empty family forces P=0. A contractible two-term complex stays contractible under an additive functor. The bounded-above hypothesis is kept for the Ext-orthogonality Hom theorem; I did not extend it to an arbitrary unbounded complex. The leaf has no exactness requirement on F; applying a right-exact but nonexact additive tensor functor is a useful check that it refers to K(A), not a claimed exact descent to D(A).

I checked B1-B10 (statement-only new tasks, self-contained objects, notion references, TeX encoding, exact labels, real searches, exact leaf and blueprint references), C1-C8 (all non-elementary facts covered by cited statements, full verbatim quote audit, no reliance on a dependency's proof, no route replacement), D1-D5 (two genuinely different nontrivial jobs plus the exact leaf, not one replacement for the whole theorem), and E1-E7 (hypotheses, coefficients, sign compatibility, and normalization). No new parent proof step exceeds 2000 characters; the maximum is the retained 1077-character normalization argument. The first new task contains several linked conclusions because its purpose is the one free-sheaf presentation of restriction, not a restatement of existence of lower shriek. The second new task is the one Hom-complex/injective-detection transfer argument. The already-existing free-Yoneda, sheafification, presentation and Ext-orthogonal-Hom nodes are identified above as their proof ingredients for subsequent workers, not replaced by duplicate copies.

The original accepted generic tool uses remain declared in split_report. They are generic derived-category/Grothendieck tools and do not replace any geometric step of the curve unit. There is no maintainer metadata edit in this repair.

## Not duplicates

- lem-trf-additive-homotopy-triangulated vs lem-sfb-module-derived-functor-compositor-shifts: the existing node normalizes specified K-flat pullbacks and K-injective pushforwards of condensed coefficient modules on schemes, including compositors and their shifts on derived categories; it does not state triangulatedness of K(F) for an arbitrary additive functor between abelian categories. The new Mathlib leaf applies to potentially nonexact additive functors and concerns homotopy categories, with no schemes, condensed coefficients or chosen resolutions.

- lem-trf-ringed-site-restriction-generator-data vs lem-coef-module-flat-cotorsion-foundation: that node proves flat/cotorsion orthogonality and a flat generator, not exact restriction or cross-site free-sheaf representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-pc-functorial-cycle-pullback-construction: that node constructs a bounded-above functorial resolution from a given cover functor, not the ringed restriction and its representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-pc-sites-modules-quotient-j-shriek: its presentation clause is reused as an ingredient; it has no second site, restriction, exactness or natural representers for the restricted-module Hom functors.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-compact-flat-generator-cover: that node constructs compact flat covers on schemes, not varying-ring restriction between arbitrary small sites.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-flat-telescope-target-refinement: that node refines flat telescope targets and constructs a cone map; the new node concerns no telescope.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-flat-telescope-arrow-bar-data: that node gives span/tower data for maps between flat telescopes; the new node concerns no telescope or tower.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-compact-flat-generator-relative-extension: that node extends maps of bounded-above complexes through flat quasi-isomorphisms; the new node is not a relative extension theorem.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-compact-flat-generator-tower-resolution: that node builds compatible compact-flat tower resolutions on schemes; the new node constructs no tower resolution.
- lem-trf-ringed-site-restriction-generator-data vs lem-pc-sites-modules-functorial-flat-cover: that node provides a flat cover functor on one site, not the stated exact restriction or cross-site Hom representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-separating-family-epi-coproduct: that abstract theorem assumes a separating family already given; it supplies no ringed restriction, free-sheaf evaluation formula or representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-sheaf-free-separator: that node uses sheaves valued in one fixed coefficient category and a fixed separator; the new node treats modules over a varying sheaf of rings and compares two sites by restriction.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-abelian-etale-sheaves-grothendieck: that node concerns Grothendieck abelian sheaves on a scheme etale site, not this arbitrary-ringed-site adjunction criterion or its free restriction representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-affine-etale-rank-one-separating: that node proves separation on affine etale objects with constant coefficients, not varying ring sheaves and exact restriction between general sites.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-constructible-generation: that node uses finite constant coefficients and qcqs schemes with constructible generators; none of these hypotheses or conclusions appears here.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-module-sheaf-colimit-constructible-cocone: that node recognizes filtered colimit cocones via constructible tests; the new node does not recognize such cocones.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-sheaf-flat-separator: that node asserts existence of a flat separator with a fixed monoidal coefficient category; it does not state the varying-ring cross-site restriction representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-module-sheaves-enough-injectives: that node only asserts enough injectives on scheme etale sites with constant coefficients; it does not prove the adjunction transfer criterion or the restriction-generator data.
- lem-trf-ringed-site-restriction-generator-data vs lem-weil-pbc-module-sheaves-grothendieck-abelian: that node proves a Grothendieck property for constant coefficients on scheme etale sites, not either new arbitrary-ringed-site argument.
- lem-trf-ringed-site-restriction-generator-data vs lem-pur-ringed-site-grothendieck-abelian: that node gives Grothendieck structure and one generator on a ringed site, but neither exact restriction nor the second-site natural representers.
- lem-trf-ringed-site-restriction-generator-data vs def-sc-etale-small-generator: that node defines one concrete abelian etale generator; it asserts no theorem about varying-ring restriction or family representers.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-etale-small-generator-sections: that node bounds the size of sections of a concrete etale generator; it asserts no restriction/presentation theorem.
- lem-trf-ringed-site-restriction-generator-data vs lem-sc-etale-small-generator-separating: that node asserts separation for one concrete etale generator, not the varying-ring restriction data.
- lem-trf-additive-homotopy-triangulated vs lem-weil-pbc-homotopic-maps-equal-cohomology: that node only says additive functors preserve chain homotopies and their cohomology consequences; the leaf gives coherent shift and distinguished-triangle preservation.
- lem-trf-additive-homotopy-triangulated vs lem-weil-pbc-exact-functor-derived-factorization: that node requires an exact functor and concludes descent to D(A); the leaf needs only an additive functor and concludes triangulatedness on K(A).
- lem-trf-ext-orthogonal-adjoint-acyclic vs lem-trf-continuous-cocontinuous-derived-shriek: the parent concludes unbounded derived lower shriek and its normalized adjunction; the new node isolates a strictly smaller prerequisite and asserts no derived-functor existence.
- lem-trf-ext-orthogonal-adjoint-acyclic vs lem-trf-derived-colimit-bar: that node computes a constant-ring derived colimit by a bar complex on an identity-cover site; the new node supplies an independent prerequisite on arbitrary ringed sites/adjunctions.
- lem-trf-ext-orthogonal-adjoint-acyclic vs lem-weil-pbc-abelian-etale-sheaves-grothendieck: that node concerns Grothendieck abelian sheaves on a scheme etale site, not this arbitrary-ringed-site adjunction criterion or its free restriction representers.
- lem-trf-ext-orthogonal-adjoint-acyclic vs lem-weil-pbc-module-sheaves-grothendieck-abelian: that node proves a Grothendieck property for constant coefficients on scheme etale sites, not either new arbitrary-ringed-site argument.

- lem-trf-ext-orthogonal-adjoint-acyclic vs lem-trf-acyclic-coproduct-ext-orthogonal-hom: the existing node proves acyclicity of Hom(P,F) in the source module category. The new node adds an adjunction into a second category, differential-compatible Hom transport and injective detection to conclude acyclicity of L(P); the existing node is its reusable input.

## What remains

Stage 1 only: the two new statement-only nodes are deliberately open for independent workers. No missing mathematical source or unresolved statement issue remains in the parent split. The required deliver.py --no-push run exited successfully: OK (not pushed), commit 4eca0a7c2a7, preflight passed. The final push is performed by deliver.py after this report is packaged.

## Live-DAG promotion return repaired (2026-10-22)

The latest return is the landing refusal that the completed side-project split was not promoted to the live queue DAG. I continued the retained four node files, full report, original-proof.json, citations and logged searches; I did not reconstruct or discard the previously approved work. The delivery command rebases these sandbox stage-1 fields by overlay onto freshly fetched current main. The live read-clone item still has the original eight-step split, while the retained replacement is the five-step, 2965-character assembly with two unsplit tasks and one Mathlib leaf. The released keep_plan repair note remains applicable. Parent statement, statement dependencies, source, blueprint and maintainer metadata agree with the live node.

The required initial dry run on this retry exited with a new duplicate-check diagnostic: the current DAG contains `lem-sfb-module-derived-functor-compositor-shifts`, sharing Stacks 014X with the retained Mathlib leaf. I opened its complete statement: its hypotheses fix condensed-ring module categories over schemes and specified derived resolutions; its conclusions identify pullback comparisons/compositors and shifts. It cannot supply arbitrary additive K(F) triangulatedness. The explicit pair comparison below repairs the current-main gate, without altering the mathematical leaf or inventing another search. Its statement and search question are unchanged, so the real logged Mathlib queries were reused.

I re-read every statement cited in the five assembly steps against the current read clone, including the partial-adjoint criterion, the module (rather than abelian-sheaf) Ext vanishing, both Grothendieck consequences, unbounded criterion, derived-functor assembly, exact localization, saturation, derived exactness, exact-functor factorization and the complete pre-derived normalized Hom formula. The old report's per-step hypothesis checks still apply: small generating family, bounded-above acyclic test complexes, exact sequential colimits, both additive adjoints, and the identity-denominator comparison are all explicitly supplied. All 17 citations remain verbatim substrings of the corresponding current statements (sandbox statements for the three new nodes). No dependency change forces a different inference or a replacement citation. The 1077-character final normalization step remains intact; no proof step exceeds 2000 characters. The empty family, zero module category, identity restriction, and nonexact additive-functor homotopy-category tests continue to satisfy the new statements.

For a reproducible statement-level record of this re-read, these are the current live dependency fingerprints:

- `lem-trf-partially-defined-module-adjoint`: statement SHA-256 `15ce74a80c3dc987b7a04d61354e0faf21e03a3b690eb8c4c0784eb416bf8c84`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`: statement SHA-256 `7a4e9f974d98422c2d52646b1c2e55bfb7526dcc2ad5bbcb3729c318e5b5ede8`.
- `lem-trf-module-pullback-injective-section-acyclic`: statement SHA-256 `dcba1faaf5d3737a9a8a203489fa7c74bbfbb7974c33e20b47052db1a1ecc8d9`.
- `prop-pur-kinjective-resolutions-exist`: statement SHA-256 `257c9618cd92575ef5e941ed6fe14f1f57c3262c71c6611e3058341d1c3d7f43`.
- `lem-sp-grothendieck-enough-injectives`: statement SHA-256 `909798e2ae7742fd9651a589ca967e0843417082f18cb0cafb5a8fff3546711d`.
- `lem-trf-unbounded-left-derived-criterion`: statement SHA-256 `2f610ef7618a3a132c6dfe8e38060ef4fc359491d375868b3ce3ea49c1bc3e40`.
- `new-everywhere-defined-derived-functors`: statement SHA-256 `d425961468f01cd2e0c529c88c8fa4414f95e817bc8ce1d4a6699fa63e51c495`.
- `lem-pur-homotopy-category-triangulated`: statement SHA-256 `e8fe9adf556e26ca2f5a98455e32214c242c74deea3ee6f74d792cde977b8695`.
- `lem-pur-quasi-isos-saturated-triangulated`: statement SHA-256 `b13f5f120689eae4804f53468c5c2a049dc5a50a7267a97586f8dae3763c4bb9`.
- `lem-pur-left-derived-exact-when-defined`: statement SHA-256 `0b983bd9a7929e03265f168cc826841d58be0ca6ceb414547ad4206874d73d63`.
- `lem-weil-pbc-exact-functor-derived-factorization`: statement SHA-256 `3ee0bb75f20234a0b53251f84ddf62e82780bf8bd4b857d6e9e1195d6bbf0288`.
- `def-pc-essentially-constant-ind-diagram`: statement SHA-256 `dc84997958dac7461fc830bc7db8d26e7b6055e105aa0e028337517dc9b4a063`.
- `lem-pc-pre-derived-adjoint-functors-general`: statement SHA-256 `17ff97eeab12b14de649d6323fcbefb72c6eae964b26e0c0e487ef5cfba0cad0`.

The original successful dry run recorded below is historical. This retry must pass a fresh current-main dry run and then push before it is reported delivered.

## Original returned proof, preserved verbatim

### Original step 1

Put $\mathcal A=\operatorname{Mod}(\mathcal O')$ and $\mathcal B=\operatorname{Mod}(\mathcal O)$. Restriction along $u$ acts on modules using $\mathcal O'(U)=\mathcal O(uU)$, so is additive and preserves kernels sectionwise. A module morphism is epic exactly when its underlying abelian-sheaf morphism is epic: its cokernel has the underlying abelian-sheaf cokernel, by the description of module cokernels. The cited general-site epimorphism criterion therefore applies. If $M\to N$ is epic and $s\in N(uU)$, choose a cover of $uU$ on which $s$ lifts to $M$. Cocontinuity gives a cover $\{U_j\to U\}$ whose images factor through that cover; restriction of the chosen lifts gives lifts in $M(uU_j)$. Thus $g^{-1}$ preserves epimorphisms as well as kernels and is exact. With the identity structural ring map there is no scalar extension: $g^*=g^{-1}$.

Uses: def-weil-sheaf-of-modules-category, lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective.

Source: literature/stacks-project/sites-modules.tex, Tag 0797, lemma-lower-shriek-modules; exactness written by local lifting from the cocontinuity hypothesis.

### Original step 2

On either ringed site $(\mathcal E,R)$ write $E_U=(R[h_U])^\#$ for the free sheaf on an object $U$. Free presheaf Yoneda followed by the sheafification adjunction gives $\operatorname{Hom}_R(E_U,M)=M(U)$, naturally in $M$. All small coproducts exist, since module sheaves form a Grothendieck abelian category. For any module $M$, take the sum of $E_U$ over all pairs $(U,s)$ with $s\in M(U)$, with its evaluation map to $M$. Every section $s$ is the image of the identity-basis section in its own summand, so this map is epic. These indexing sets lie in the fixed module universe. Let $\mathcal P$ be all small sums of the $\mathcal O'$-module generators $E_U$; it contains $0$, is closed under finite sums and epimorphically generates $\mathcal A$.

Uses: lem-weil-pbc-free-yoneda-presheaf-module, def-weil-presheaf-modules-sheafification, prop-pur-kinjective-resolutions-exist.

Source: literature/stacks-project/sites-modules.tex, Tag 03EW, lemma-module-quotient-flat, proof of (3), and the evaluation calculation in Tag 0797, lemma-lower-shriek-modules.

### Original step 3

For each $U\in\mathcal C$ and $N\in\mathcal B$, the preceding evaluation bijections give $\operatorname{Hom}_{\mathcal A}(E_U,g^{-1}N)=N(uU)=\operatorname{Hom}_{\mathcal B}(E_{uU},N)$. For a sum $P=\bigoplus_i E_{U_i}$ the corresponding object of $\mathcal B$ is $\bigoplus_i E_{uU_i}$: maps out of either sum are precisely tuples of maps out of its summands. This supplies the natural representing bijections for every $P\in\mathcal P$. Apply the partial-adjoint extension criterion to obtain $g_!\dashv g^{-1}$. Additivity follows directly from its natural Hom bijections: the transpose of $g_!(a+b)$ is the sum of the transposes of $g_!a$ and $g_!b$, because $g^{-1}$ is additive. The colimit-preservation theorem for left adjoints gives preservation of all small colimits, hence right exactness (finite colimits) and preservation of sequential colimits. In particular $g_!E_U\cong E_{uU}$ by their representing bijections.

Uses: lem-trf-partially-defined-module-adjoint, lem-weil-pbc-left-adjoint-preserves-colimits.

Source: literature/stacks-project/sites-modules.tex, Tag 0797, lemma-lower-shriek-modules, its Hom computation and application of Tag 0793; colimit observation in sites-cohomology Tag 07AC, lemma-existence-derived-lower-shriek.

### Original step 4

Let $I$ be any injective object of $\mathcal B$ and put $F=g^{-1}I$. The module-coefficient acyclicity theorem gives $\operatorname{Ext}_{\mathcal O'}^p(E_U,F)=0$ for every $U\in\mathcal C$ and $p>0$. It applies to the actual ring sheaves $\mathcal O,\mathcal O'=g^{-1}\mathcal O$ and does not require $F$ itself to be injective. The $E_U$ here are exactly the free sheaves of step 2.

Uses: lem-trf-module-pullback-injective-section-acyclic.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6X, lemma-pullback-injective-pre-limp, and the Ext display in Tag 07AC, lemma-existence-derived-lower-shriek.

### Original step 5

Let $P^\bullet$ be bounded above, acyclic, with terms in $\mathcal P$. Apply the Ext-orthogonal-sums Hom lemma to the family $(E_U)_U$ and $F=g^{-1}I$ using step 4. It gives acyclicity of $\operatorname{Hom}_{\mathcal A}(P^\bullet,g^{-1}I)$. The ordinary adjunction identifies this complex with $\operatorname{Hom}_{\mathcal B}(g_!P^\bullet,I)$ degree by degree; naturality intertwines precomposition with each differential, including the sign $(-1)^{n+1}$. Thus the latter Hom complex is acyclic for every injective $I$. This forces $B^\bullet=g_!P^\bullet$ to be acyclic: if $H^r(B)\ne0$, embed it in an injective $I$ (enough injectives follow from the cited Grothendieck theorem). Its inclusion gives a nonzero map $Z^r(B)/\operatorname{im}d^{r-1}\to I$. Extend this map along the monomorphism $Z^r(B)/\operatorname{im}d^{r-1}\hookrightarrow B^r/\operatorname{im}d^{r-1}$ using injectivity. The resulting map $B^r\to I$ is a cocycle in $\operatorname{Hom}(B,I)$, since it kills $\operatorname{im}d^{r-1}$, and is not a boundary, since every boundary factors through $d^r$ and vanishes on $Z^r(B)$. This contradicts acyclicity of that Hom complex.

Uses: lem-trf-acyclic-coproduct-ext-orthogonal-hom, prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives, def-sp-injective-resolutions.

Source: literature/stacks-project/sites-cohomology.tex, Tag 07AC, lemma-existence-derived-lower-shriek, verification of condition (2), with its injective-detection argument expanded.

### Original step 6

Apply the unbounded left-derived criterion with $F=g_!$ and $\mathcal P$ from step 2. Hypothesis (1), including the zero object and finite sums, is step 2. Hypothesis (2), preservation of bounded-above acyclic $\mathcal P$-complexes, is step 5. Both $\mathcal A$ and $\mathcal B$ are Grothendieck abelian by the ringed-site theorem, so sequential colimits exist and are exact: $\mathbf N$ is a filtered small category. Step 3 gives right exactness and commutation with those colimits, completing (3)-(5). Hence the denominator pro-diagram for $Q g_!$ is essentially constant at every complex, with no boundedness restriction. The assembly theorem supplies the functor $Lg_!$ and its canonical derived comparison $\varepsilon:Lg_!Q\to Qg_!$.

Uses: lem-trf-unbounded-left-derived-criterion, prop-pur-kinjective-resolutions-exist, new-everywhere-defined-derived-functors.

Source: literature/stacks-project/sites-cohomology.tex, Tag 07AC, lemma-existence-derived-lower-shriek, application of derived.tex Tag 0794, proposition-left-derived-exists, conditions (1)-(5); derived-functor assembly.

### Original step 7

For an additive functor, applying it termwise commutes with the shift and with the cone: the cone differential is the matrix with entries $d_Y,f,0,-d_X$, and its image is the same matrix with the functor applied to each entry. It also carries $dh+hd$ to the same homotopy formula, so descends to homotopy classes. Thus $K(g_!)$ carries cone triangles to cone triangles. By the cited triangulations and exactness of localization, $QK(g_!)$ is exact. The quasi-isomorphisms form the saturated, triangulation-compatible multiplicative system required by Situation 05S8. Step 6 gives definedness everywhere in precisely that situation. The everywhere-defined-left-derived exactness theorem therefore gives $Lg_!$ its canonical triangulated structure.

Uses: lem-pur-homotopy-category-triangulated, lem-pur-quasi-isos-saturated-triangulated, lem-pur-left-derived-exact-when-defined.

Source: literature/stacks-project/derived.tex, Tags 014X (lemma-additive-exact-homotopy-category), 05SE (proposition-derived-functor), applied to the functor of Tag 07AC.

### Original step 8

Since $g^{-1}$ is exact, its termwise functor descends to derived categories by the exact-functor factorization theorem. Its right-derived denominator ind-diagram at $N$ is essentially constant with value $Qg^{-1}N$: each leg $Qg^{-1}N\to Qg^{-1}I$ over a quasi-isomorphism $N\to I$ is an isomorphism, whose inverse defines the representing cocone. The identity denominator gives a section, and a common later denominator verifies the common-stage condition, since the legs commute. Use this cocone, whose leg at the identity is $1$, and the pro-cone for $Lg_!$ from step 6 in the canonical pre-derived adjunction theorem for $g_!\dashv g^{-1}$. Its bifunctorial bijection gives $Lg_!\dashv g^{-1}$. For the asserted chain map $f:g_!C\to N$, specialize that theorem to identity denominators $s=1_N$, $t=1_C$ and its map $C\to g^{-1}N$ equal to $f^\flat$. Its formula reads $e(Q(f^\flat))=Q(f)\circ\varepsilon_C$. The inverse bijection is exactly the displayed adjunction in the item; hence it sends $Q(f)\circ\varepsilon_C$ to $Q(f^\flat)$, proving the specified normalization.

Uses: lem-weil-pbc-exact-functor-derived-factorization, def-pc-essentially-constant-ind-diagram, lem-pc-pre-derived-adjoint-functors-general.

Source: literature/stacks-project/derived.tex, Tag 0DVC, lemma-pre-derived-adjoint-functors (via its formula in Tag 0FND), and Tag 09T5, lemma-derived-adjoint-functors, with exact right adjoint.

