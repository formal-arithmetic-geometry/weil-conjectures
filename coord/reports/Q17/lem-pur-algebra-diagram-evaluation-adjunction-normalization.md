## Worker report

Item: lem-pur-algebra-diagram-evaluation-adjunction-normalization. Group Q17. Stage 1 only, 2026-10-22.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-algebra-diagram-evaluation-adjunction-normalization.json: unchanged statement, eight proof steps, exact dependency union, agent proof origin and split report. Blueprint ancestry and creation fields retained.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: worker report and direct-delivery review.

No Lean writing, compiler, Lake, local checker, repository mutation or manual git command.

## New nodes

None. Zero new Mathlib leaves. The singleton-extension generalization investigated during research is not delivered: existing free-diagram and ringed-topos comparison statements suffice.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag and diagram adjunction, evaluation/counit and ringed-diagram notions found no project declaration stating every clause.

## WANTED

None.

## Sources and searches

Read sites-cohomology.tex, Tag 07A6, lemma-adjoint, and Tag 0D6E, lemma-derived-pushforward-composition, including its proof via pullback composition and uniqueness of adjoints. Read Tag 0941, lemma-derived-limit-is-ok: its evaluation-preserves-K-injectives argument concerns constant abelian towers and cannot be applied to varying rings without justification. Read derived.tex, Tag 09T5, lemma-derived-adjoint-functors, and the preceding general Hom calculation. Read Zheng, Construction 4.1, printed page 21, for evaluation and its generally nonexact module singleton left extension.

Read the chapter record and unit sk-thm-sf-compatibility, especially the coefficient clause preserving specified counits and evaluations. The main-20261015 ancestor thm-pur-rational-and-qbar-purity Step 2 transports finite-stage purity; the existing blueprint.from.place records the intervening normalization auxiliary and is retained. No geometric route changes and no SGA sources.

DAG and whole-blueprint searches included singleton, singleton extension, diagram evaluation, evaluation extension, evaluation, free diagrams, evaluation adjunction, restriction pushforward and derived adjunction. Opened the existing singleton geometric/scalar comparisons and system evaluation scalar normalization. Those restrict to inverse sequences or extra coefficient hypotheses. Instead this proof uses the existing general free-diagram adjunction and ringed-topos tools, with no new node.

All Mathlib searches were executed through msearch.py, with results in searches.jsonl. The item was searched with LeanFinder, Loogle, grep and LeanSearch. The Loogle evaluation/counit query found ordinary evaluation adjunction counits. Read Mathlib/CategoryTheory/Adjunction/Evaluation.lean lines 38-67: its coproduct construction and Hom bijection are already represented by lem-weil-pbc-evaluation-free-diagram-adjunction. LeanSearch found ordinary module restriction and presheaf pushforward formulas; LeanFinder found ordinary sheaf module adjunctions. Alternative singleton and derived induction phrasings found sheafification, Kan extension and ordinary scalar extension, without the asserted unbounded varying-ring coherence. Earlier item search records are retained. No invented searches or unavailable-as-no-match records.

## What changed and what was wrong

The item had an empty proof. Its statement is unchanged and no statement dispute was found. The proof avoids the false shortcut that varying-ring evaluation preserves K-injectives and avoids cancelling a derived coefficient-forgetting functor on morphisms. Constant-A evaluation does preserve K-injectives. Ringed-topos composition then proves that evaluated K-injective B-diagrams compute the level direct image. Common-resolution representatives prove the coefficient equation.

No clause is left unfinished. Delivery status is determined by the server checks and final command.

## Review by Q17

I opened the item and every cited statement and read the source places above. This is an agent coherence argument using the Stacks machinery, not an assertion that Tag 0941 itself states the arbitrary algebra-diagram theorem. The coefficient isomorphism u^{-1}B_Y=B_X makes the geometric inverse images exact at both diagram and level categories. Flatness of A to B_j or of transitions is never used.

Step 1 uses the general small vertical site of lem-weil-pbc-diagram-site-realization. The varying-ring sheaf and its module equivalence are explicitly unpacked from the module-sheaf definition on vertical slices, rather than borrowed from the constant-ring module-equivalence theorem. Kernels and sheafified cokernels carry their induced ring actions. The exact-functor cohomology statement gives exactly preservation/detection of quasi-isomorphisms; coefficient restriction leaves the underlying abelian sheaf unchanged and reflects zero. prop-pur-kinjective-resolutions-exist is stated for any small commutative ringed site, so applies to both diagram and level sites. This step is elementary construction/unpacking with the existence theorem cited explicitly.

Step 2 uses the actual Hom bijection of the free-diagram adjunction, with all arrows j to k, not just full faithfulness of an embedding. Exactness of its coproduct formula follows from filtered finite subsums and the cited Grothendieck ring-module statement's exact filtered colimits. The exact-left-adjoint criterion is therefore applicable to constant-ring evaluation. The ordinary module adjunction gives the component counit, and the exact-square derived-counit statement gives the required derived equation. Its preservation-of-K-injectives hypothesis is established here only for constant coefficients. Smallness covers all coproduct indices.

Step 3 uses the stated two-factorization normalization of lem-pur-diagram-ring-restriction-pushforward. For each singleton, the restriction-ringed-topos statement identifies restriction with identity-topos direct image. The precise derived-composition statement says that direct image of the replacement of f_*I is a quasi-isomorphism and represents the comparison; these are exactly the maps a:U_XI to H and c:U_{X,j}K to L. Exact-functor localization identifies right-derived restriction with termwise restriction. The other factorization is computed directly because geometric direct image is right adjoint to an exact inverse image, hence preserves K-injectives by the criterion already cited. No preservation by coefficient restriction is assumed.

Step 4 carries the acyclicity argument itself. The resolution theorem supplies a,b,c. Only H_j is asserted K-injective, from constant-coefficient evaluation in step 2. The K-injective Hom bijection gives h:H_j to L, a homotopy equivalence, with ha_j=cU(b) in the homotopy category. Additive direct image preserves that equation and homotopy equivalences. The quasi-isomorphisms supplied by step 3 and two-out-of-three force f(Ub), then f_j(b), to be quasi-isomorphisms. Detection uses exact coefficient restriction and cohomology, not faithfulness on derived morphisms. The derived-map computation gives the canonical unit through the replacement b. Thus I_j computes the level direct image without being declared K-injective.

Step 5 defines beta by the actual derived comparison on a K-injective B-diagram. The cited K-injective Hom and derived-map statements cover all derived morphisms and the resolution-change cocycle, so the construction is natural and independent of resolutions. Lambda is exact localization of componentwise inverse image with the pulled-back ring action. The ordinary module-adjunction statement says exactly which ring actions and transpose are in use.

Step 6 uses the full normalized Hom formula of the exact-square derived-counit theorem separately for each adjunction, setting its restriction functors to identities. Thus that use does not impose preservation by varying-ring evaluation. A map into K-injective I is represented by a chain map. Its ordinary component transpose is exactly the one furnished by the module adjunction. The general target I_j is permitted in the normalized formula; alternatively compose with b:I_j to K and use naturality of the derived unit. This proves the equation on actual derived Hom sets. Taking the transpose of the counit gives the counit equation with lambda in the direction printed in the item. It also pins beta to the specified module-induced mate.

Step 7 checks the precise coefficient equation. Derived-composition normalization represents its routes by Qf(a_j) and Qf(cU(b)). The K-injective derived-map statement identifies target changes with the homotopy equivalence h of step 4, whose equation identifies these representatives. The equality holds in the target A-derived category before taking cohomology. There is no cancellation of a nonfaithful derived restriction.

Step 8 handles any arrow alpha:j to k, using its actual scalar-restriction transition. The same restriction/topos composition comparison applies to B_j to B_k without flatness. Natural derived-unit equations and resolution computation identify both transition routes with Qf_j(z_alpha) followed by the appropriate derived unit; the normalized restriction comparison makes these the same unit after target identification. This is equality in the derived category over B_{Y,j}, not an inference from levelwise detection of morphisms of systems. Identities and composite arrows use the actual diagram laws.

B1-B10: no new nodes, hollow definitions, invented notions or statement changes; TeX is single-escaped after JSON decoding; all sources and search logs are retained. C1-C8: each cited statement was read, and citations.json quotes it verbatim. General off-unit tools are declared in split_report.tool_uses; these supply module categories, resolutions, ordinary adjunctions or derived normalization, and do not replace the geometric route. D1-D5: no content is moved into a new node; the argument occurs in the item's steps. A dependency-closure traversal found no path back to this item. All eight steps are below 2000 characters.

For E, checked empty J (no j-dependent assertions), singleton J (ordinary ringed-topos adjunction and restriction), discrete multi-object J (projections), parallel arrows and one-object monoid categories (all arrows appear in the free adjoint and transition verification), zero ring and zero complex (zero/identity maps), and the nonflat arrow Z to Z/2. In the latter case the singleton module left extension need not be exact; it is not used. Constant-Z evaluation still has its exact free-diagram adjoint. All Hom and resolution statements are unbounded; no product exactness, completeness, perfectness or cohomological bound is invoked.

There was no second worker: this is the explicitly authorized direct-delivery self-review. The maintainer's independent mathematical review remains.
