# Worker report: lem-sfb-finite-field-closed-support

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-closed-support.json`: existing statement, unchanged; repaired split, with a 2689-character five-step proof assembly.
- `dag/nodes/sec-six-functors-basics/lem-sfb-intrinsic-finite-derived-pullback.json`: new statement-only node, status `unsplit`, no proof steps or proof dependencies; Mathlib verdict: no match.
- `citations.json`: verbatim statement quotes for every citation in every parent proof step.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the item tag and the closed-support/pullback concepts, and read `lean/Sheaf/Paper/FiniteFieldClosedSupport.lean`. The latter's exact public theorem `AlgebraicGeometry.Scheme.finiteFieldClosedSupport_bounded_constructible` ends in `sorry` (line 130), so it is not an attachment. The closed ordinary étale result and `Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar` in `WeilConjectures/CategoryTheory/DerivedCategory/Constructible.lean` concern the small étale site, not the intrinsic constant-ring pro-étale category here. No Lean file was written or compiler run.

## WANTED

None. Bhatt–Scholze and the relevant Stacks sources are present locally.

## Return repaired

The human asked to spread the 4038-character proof over independent work items, retaining the statement and every argument, with a parent assembly of at most 3000 characters and at least one new statement-only unsplit node. I extracted old steps 2–3 together as `lem-sfb-intrinsic-finite-derived-pullback`. This is a separate problem about arbitrary ordinary inverse images; it neither mentions exceptional inverse image nor concludes the parent's closed-support assertion. Its statement specifies exactness, the natural cohomology comparison, the pulled-back strata, the comparison of restrictions, the same finite local models on the actual pulled-back cover, and the unchanged vanishing interval. These are exactly the two substantial arguments removed from the parent, not an opaque restatement of the desired preservation result.

The geometric argument remains parent step 1 (old step 1), the application of the existing direct-image theorem remains parent step 3 (old step 4), the rotated support triangle remains parent step 4 (old step 5), and the termwise closed-counit recovery remains parent step 5 (old step 6). Parent step 2 applies the new node to both morphisms. The new child's roughly 2k-character statement describes all its outputs and has no proof sketch or steps; its full proof handoff appears below, as the original argument, for a future worker. The complete old six-step argument is preserved below so that no argument is lost during extraction. The parent's remaining steps are each at most 697 characters. I did not manufacture new nodes for the geometric two-line applications or the triangulated-category rotation; those stay as explicit assembly arguments using existing statements.

## Source and route

I read Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 6.7.11 and its proof: the closed-support triangle, two uses of inverse-image preservation, and direct-image constructibility. I also read Lemma 6.5.8(1)–(2) and Lemma 6.5.9(5), with their proofs, for the new child's finite-discrete specialization. With R=A and m=0, completion adds no condition. The source gives the immersion pullbacks needed by the parent. The child records their general constant-coefficient version: the preserved exactness/stratification argument below works for every scheme morphism, without qcqs or Noetherian assumptions; this generality is proved by that argument, not asserted to follow from a bare application of the adic lemma.

For the local-model ingredient I read Stacks `sites-modules.tex`, Tag 093R, `lemma-pullback-locally-constant`, and the existing finite-model node's precise statement; for constructible strata I read Stacks `morphisms.tex`, Tag 054I, `lemma-inverse-image-constructible`, including its retrocompact-open base-change proof. These are supporting sources via existing nodes, not newly claimed general theorems without dependencies. The current blueprint unit is `sk-def-sfb-dc-restricted-functors`; its chapter route and its internal-Hom residue-field reduction are unchanged. `blueprint_refs.py ancestor` gives `lem-sfb-dc-hom-preserves`. The child's via chain is the item followed by `lem-sfb-finite-field-internal-hom-finiteness`. No forbidden source is used for any assertion.

## Search record

There were no retained node files, report, or search log in this Q49 sandbox, only `.brief*` markers. I therefore copied the current live item as the repair baseline, retained all its prior citations/provenance/search records, and kept a local `original-node.json` for the proof-preservation check. There was no stale sandbox split to dry-run first. The delivery tool rebases the split-owned fields onto current server main and keeps maintainer metadata.

For duplicates I searched the whole `dag/nodes/` by statements, not merely proof text, for combinations of inverse image/pullback with constructibility on pro-étale sites, and inspected all plausible candidates listed below. I searched the whole imported blueprint with `blueprint_refs.py search` for `pullback constructible`, `proetale constructible pullback`, `pro-étale constructible pullback`, `constant cohomology`, `constructible cohomology`, `pullback`, and `exact pullback`; none states the new intrinsic ordinary-module theorem. I also searched the source by notion and read the ordinary étale derived-pullback declaration and the relevant intrinsic finite-local-model theorem. No exact project attachment was found.

Every new-node Mathlib query was actually run with `batch2/msearch.py Q49 lem-sfb-finite-field-closed-support`; `searches.jsonl` contains the original records. Two distinct LeanFinder phrasings returned generic sheaf-pullback finite-limit lemmas and locally constant condensed-module functors. Loogle's `"SheafOfModules", "pullback"` query returned presheaf module pullback constructions and adjunctions, not constructibility; its second query `"Constructible", "pullback"` returned no hits. LeanSearch returned generic constant sheaf and condensed discreteness facts. Both grep phrasings returned no hits. None supplies both the intrinsic finite-stratification assertion and its ordinary derived cohomology comparison in one line, so the child remains unsplit, not Mathlib. The item's existing search records are preserved without pretending that I reran them.

## Not duplicates

- lem-sfb-intrinsic-finite-derived-pullback vs lem-sfb-pullback-constant-model-constructible: the existing node is about module objects over pulled-back condensed coefficients and finitely presented scalar presentations; the new node uses actual ordinary constant-ring module sheaves, intrinsic finite local models and an exact termwise ordinary derived functor with its natural cohomology comparison. There is no coefficient-category identification silently imported.
- lem-sfb-intrinsic-finite-derived-pullback vs lem-weil-pbc-module-constructible-pullback: the existing node treats internal module objects and local cokernel presentations over arbitrary condensed ring objects; it does not state the ordinary constant-ring sheaf result, its local constant models, or the derived/cohomology comparison.
- lem-sfb-intrinsic-finite-derived-pullback vs lem-weil-pbc-finite-pullback-constructibility: the existing statement fixes an adic datum, positive quotient A/I^(n+1), actual finite-function coefficients and restriction along pbcLevelConstantComparison, and explicitly excludes derived objects/support intervals. The new node is directly about ordinary constant finite-field modules and their ordinary derived inverse image.
- lem-sfb-intrinsic-finite-derived-pullback vs lem-pe-coefficient-finite-local-model-pullback: the existing statement assumes an inverse image already has finite locally constant models, and only states their preservation under a further inverse image plus isomorphism invariance. It neither produces global constructible strata from an intrinsic constructible module nor gives exactness or the derived cohomology statement.
- lem-sfb-intrinsic-finite-derived-pullback vs lem-exc-proetale-pullback-locally-constant: the existing node supplies the finite constant models after pulling back one locally constant module. The new problem must also construct and identify the pulled-back strata, prove module exactness, and descend termwise pullback to the ordinary derived category with bounded cohomology. It is more than a restatement of that input.
- lem-sfb-intrinsic-finite-derived-pullback vs lem-weil-pbc-exact-functor-complex-cohomology: the existing node gives a natural cohomology comparison conditional on an exact functor; the child must establish exactness for the actual module inverse image and the intrinsic geometric constructibility statement.

## Review by Q49

I checked the return against the live node, its Lean docstring and theorem, the sources above, and the statements of every dependency used in the new assembly. The item statement is byte-for-byte unchanged. The new child's objects and all conventions are introduced in its own statement, with definition dependencies for the scheme, sites, coefficients, module categories, ordinary derived category, actual module inverse image and intrinsic constructibility. Its proof and proof_deps are empty, its status is unsplit, and its Mathlib records correspond exactly to searches that ran. In particular I did not move a proof sketch into its statement.

Parent step 1 uses `lem-weil-pbc-finite-type-over-noetherian` exactly for finite type over a Noetherian base, and `lem-weil-pbc-noetherian-open-subscheme-noetherian` for an arbitrary open subscheme being Noetherian/quasi-compact. Applying the latter to the open inverse image of each affine proves quasi-compactness of j; it is not falsely being read as a theorem about arbitrary non-Noetherian open immersions. The spectrum of a field is Noetherian directly (its only ideals are zero and one). `lem-weil-pbc-immersion-base-change-lft` clause (2) gives local finite type of j; `def-weil-finite-type-morphism` combines it with quasi-compactness. `lem-sfb-finite-type-composition-base-change` clause (1) then gives U finite type over k. These are exactly the hypotheses required later; no separatedness of T is inserted.

Parent step 2 cites the new node's actual output for h=j and h=g. Both are genuine scheme morphisms and A is a finite field. The new statement includes exactness and the natural cohomology comparison, not merely a definition of pullback. Thus step 5 may also use the exactness established in this earlier step. The extracted proof checks constant-ring compatibility with `prop-weil-pbc-proetale-constant-ring-map` and the actual tensor/scalar construction in `def-weil-proetale-inverse-image`. `lem-weil-pbc-site-pullback-abelian-exact` really states exactness of abelian inverse image, and `lem-weil-pbc-exact-functor-complex-cohomology` really gives the natural termwise cohomology comparison. Module kernels and cokernels have the induced actions, so this passes to module sheaves without a flatness hypothesis on an unrelated ring map.

For the child's stratification assertion, `def-weil-proetale-constructible-sheaf` supplies a finite locally closed constructible stratification with locally constant restrictions and finite geometric stalks. The pullback of each immersion is an immersion by clause (1) of `lem-weil-pbc-immersion-base-change-lft`; `lem-pur-scheme-constructible-preimage` actually asserts constructibility of preimages without a finite-type hypothesis. `lem-pur-proetale-module-pullback-composition` identifies the actual restrictions, and `lem-exc-proetale-pullback-locally-constant` gives the same finite models on the actual base-changed covers, including empty covering members. For a nonempty trivialization its constant model is the geometric stalk at any geometric point, hence finite; empty trivializations may be discarded or replaced by the zero model. Since A is a finite field, finite A-modules are precisely finite-dimensional ones. These observations bridge the finite-stalk definition and the finite-model formulation; no sheaf is assumed to descend from the étale site. Exactness then keeps the entire vanishing interval, not only a single degree.

Parent step 3 uses only `lem-sfb-finite-field-proetale-direct-image` for f=j and the input furnished by step 2. I read its statement: it is on the same ordinary constant-field module categories, for finite-type k-morphisms between finite-type k-schemes, and places no global cohomological-dimension or algebraic-closedness condition on k. Step 1 verifies precisely these geometric hypotheses.

Parent step 4 uses `lem-exc-proetale-support-triangle` with Noetherian T and complementary (g,j), in ambient ordinary categories with arbitrary K. Its statement supplies g_*Rg^!K, not a constructible-restricted adjoint. Uniqueness of right adjoints is the direct Hom/Yoneda identification, so there is no replacement by an assumed constructible shriek functor. `lem-weil-proetale-dbc-triangulated` explicitly gives closure under isomorphisms, shifts and triangle extensions for the same intrinsic constructibility predicate. Rotation gives outer terms Rj_*j^*K[-1] and K, hence gives C. This step retains the original argument rather than concealing it in a new lemma that restates the parent.

Parent step 5 uses the exactness in step 2, the sheaf counit isomorphism from `lem-exc-proetale-closed-fully-faithful`, and exactness of g_* from `lem-exc-proetale-closed-exact`. The latter requires quasi-compactness of the complementary open, checked in step 1; it does not assume finite cohomological dimension. Applying the sheaf counit to every degree of a representative complex gives the actual derived isomorphism g^*g_*Rg^!K ≅ Rg^!K. Thus constructibility/boundedness of g^*C from step 2 transfers by the explicit isomorphism-invariance clause of `lem-weil-proetale-dbc-triangulated`.

I checked B–E against these statements: self-contained statements, no proof in the unsplit child, actual queries rather than invented searches, blueprint ancestor/via chain, no duplicate or parent-clause node, and no circular dependency (the child's statement dependencies are definitions only). All off-unit black boxes remaining in the parent retain their declarations in split_report.tool_uses. I checked edge cases h with empty source or target, empty strata/cover members, h=id, zero complexes, arbitrary vanishing intervals, Z empty, Z=T, and a nonreduced closed subscheme. Empty strata may be discarded; for an empty source the zero sheaf on the empty stratum witnesses constructibility. Neither the child nor parent uses a perfection/separable-closedness/CD assumption on k. The only repair is the requested extraction and replacement by its application; there is no statement dispute or hidden weakening.

## Preserved original argument and child proof handoff

The following is the live six-step proof at the repair baseline, unchanged. Old steps 2 and 3 are the complete proof handoff for the new independent child; every other step remains explicitly in the parent assembly with its citations and indices updated. Keeping this text in the report does not split the child: another worker receives its statement-only node and can implement this independent argument.

### Original step 1 — retained assembly argument

Let $j:U=T\setminus g(Z)\hookrightarrow T$ be the complementary open immersion. The spectrum of the field $k$ is Noetherian, so [lem-weil-pbc-finite-type-over-noetherian] makes $T$ Noetherian. By [lem-weil-pbc-noetherian-open-subscheme-noetherian], $U$ is Noetherian and every open subset of $T$ is quasi-compact. Hence $j$ is quasi-compact: the inverse image of an affine open of $T$ is an open subset of this Noetherian space. By [lem-weil-pbc-immersion-base-change-lft] it is locally of finite type, hence finite type by [def-weil-finite-type-morphism]. Applying [lem-sfb-finite-type-composition-base-change] to $U\to T\to\operatorname{Spec}k$ makes $U$ finite type over $k$. Thus the support-triangle theorem applies to $(g,j)$, and the finite-field direct-image theorem applies to $j$.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-immersion-base-change-lft, def-weil-finite-type-morphism, lem-sfb-finite-type-composition-base-change.

### Original step 2 — child proof handoff

For $h=j$ or $h=g$, [prop-weil-pbc-proetale-constant-ring-map] identifies $h^{-1}A_T$ with the constant ring on its source. In [def-weil-proetale-inverse-image], extension along this isomorphism merely identifies scalar actions. The underlying abelian inverse image is exact by [lem-weil-pbc-site-pullback-abelian-exact]; kernels and cokernels of module sheaves have their induced scalar actions, so $h^*$ is exact as well. Therefore [lem-weil-pbc-exact-functor-complex-cohomology] gives $\mathcal H^q(h^*K)\cong h^*\mathcal H^q(K)$ for every complex $K$ and integer $q$, with $h^*$ applied termwise on the ordinary derived category. In particular, pullback preserves the cohomological vanishing interval.

Cited nodes: prop-weil-pbc-proetale-constant-ring-map, def-weil-proetale-inverse-image, lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-exact-functor-complex-cohomology.

### Original step 3 — child proof handoff

The same pullbacks preserve constructible cohomology. For a finite stratification $T=\coprod T_a$ as in [def-weil-proetale-constructible-sheaf], put $S_a=S\times_TT_a$ ($S$ the source of $h$): its projection $i'_a$ to $S$ is an immersion by [lem-weil-pbc-immersion-base-change-lft], and $h\circ i'_a=i_a\circ h_a$. The $S_a$ partition $S$ into finitely many locally closed subsets, constructible by [lem-pur-scheme-constructible-preimage]. By [lem-pur-proetale-module-pullback-composition], $i_a'^*h^*F\cong h_a^*i_a^*F$, and [lem-exc-proetale-pullback-locally-constant] gives this a covering with the same finite $A$-module models, hence finite geometric stalks. Finite $A$-modules are finite-dimensional. With step 2, $h^*\mathcal B_A(T)\subseteq\mathcal B_A(S)$. Empty strata are discarded.

Cited nodes: def-weil-proetale-constructible-sheaf, lem-weil-pbc-immersion-base-change-lft, lem-pur-scheme-constructible-preimage, lem-pur-proetale-module-pullback-composition, lem-exc-proetale-pullback-locally-constant.

### Original step 4 — retained assembly argument

Fix $K\in\mathcal B_A(T)$. Step 3 gives $j^*K\in\mathcal B_A(U)$. Apply [lem-sfb-finite-field-proetale-direct-image] to the finite-type map $j$ of step 1: $Rj_*j^*K\in\mathcal B_A(T)$. The field and coefficient hypotheses are exactly the ones in this item; that theorem does not assume a cohomological-dimension bound on $k$.

Cited nodes: lem-sfb-finite-field-proetale-direct-image.

### Original step 5 — retained assembly argument

By [lem-exc-proetale-support-triangle], in the ambient ordinary derived category there is a distinguished triangle $C\to K\to Rj_*j^*K\to C[1]$, where $C=g_*Rg^!K$. Its exceptional inverse image is the right adjoint of the same closed direct image as in the statement; uniqueness of right adjoints identifies any choices. By [lem-weil-proetale-dbc-triangulated], $\mathcal B_A(T)$ is invariant under isomorphisms and shifts and is closed under triangle extensions. Rotate the triangle to $Rj_*j^*K[-1]\to C\to K\to Rj_*j^*K$. Its outer vertices lie in $\mathcal B_A(T)$ by step 4 and the hypothesis on $K$, so $C\in\mathcal B_A(T)$.

Cited nodes: lem-exc-proetale-support-triangle, lem-weil-proetale-dbc-triangulated.

### Original step 6 — retained assembly argument

Apply $g^*$ to $C$. Step 3 gives $g^*C\in\mathcal B_A(Z)$. The counit $g^*g_*M\to M$ is an isomorphism for every module sheaf $M$ by [lem-exc-proetale-closed-fully-faithful], and $g_*$ is exact by [lem-exc-proetale-closed-exact], since its complementary open immersion is quasi-compact by step 1. Both functors therefore descend termwise to ordinary derived categories; applying the sheaf counit degree by degree to any representative of $Rg^!K$ yields $g^*g_*Rg^!K\cong Rg^!K$. Consequently $Rg^!K\in\mathcal B_A(Z)$ by the isomorphism invariance in [lem-weil-proetale-dbc-triangulated]. When $Z$ is empty the value is zero, and when $Z=T$ the same counit identifies the value with $K$; these include the boundary cases. No step uses finiteness of the absolute cohomological dimension of $k$.

Cited nodes: lem-exc-proetale-closed-fully-faithful, lem-exc-proetale-closed-exact, lem-weil-proetale-dbc-triangulated.

## Unfinished work

The new independent node is deliberately unsplit for another stage-1 worker. No part of the parent's natural-language argument is omitted. This delivery does not implement any Lean proof or modify any Lean statement.
