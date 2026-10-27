## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-tower-adjunction-realization.json`: statement, split in eight steps; no exact Mathlib match for the full assertion.
- No new nodes and no new Mathlib leaves. `citations.json` quotes the statements of all nodes used, once per proof-step citation. `searches.jsonl` records five actual searches for the item, including a second semantic phrasing.

## Attachments

None. Searches under `lean/WeilConjectures/` for the blueprint id, strict towers, tower adjunctions, and constant-ring comparisons found no declaration stating every clause of this item. The similarly named compactification tower is unrelated. Individual module adjunctions are not an attachment for this conjunction.

## WANTED

None. All sources used are present locally.

## What was wrong or changed

The live item had a complete statement but no proof. Its statement and all maintainer-owned fields are unchanged. In particular I retained the created record, chapter, unit, source, and blueprint ancestry through `lem-cbc-strict-tower-proper-open-calculus`. The eight new proof steps establish constant-ring coherence, ordinary exact tower adjunctions, diagram-site Grothendieck realization, K-injective preservation, total unbounded derivation, its normalized adjunction, ordinary open adjunctions, and their derived descent.

The finite-ring theorem `prop-weil-pbc-proetale-constant-ring-map` does not supply arbitrary coefficients. I instead use the existing `lem-pur-proetale-constant-coefficient-comparison`, whose statement explicitly permits any commutative ring. Likewise the definition of strict tower operations is not cited as evidence that those operations exist. The generic existence and adjunction theorems supply that evidence. `lem-pc-derived-adjoint-functors` has a reversed Hom expression in its displayed conclusion; it is not used. The fully typed fraction characterization in `lem-pc-pre-derived-adjoint-functors-general` has the needed direction and normalization.

The blueprint ancestor in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-adic/thm-cbc-complete-proetale.md` states naturality and coherence, but contains no proof of this extracted foundational claim. The supplied unit record is `sk-prop-sf-cbc`; it has no proof steps. I preserve the assigned node's unit and ancestry, supply an agent-written proof from the cited Stacks facts, and declare the existing general ringed-site/derived-category results as tools. No compact-support base-change route is replaced. This is not the key node of the unit, so no unit realization file is edited.

## What could not be finished

Nothing mathematical remains in this item's one-level split. Its existing dependencies retain their own stage-1 obligations. No Lean was written or compiled.

## Not duplicates

No nodes were created. Searches of the whole DAG by constant coefficient comparison, ringed-topos module adjunction, exact site pullback, diagram-site realization, K-injective/derived existence, and open localization found the sixteen cited dependencies. Whole-blueprint searches using `tools/blueprint_refs.py search` included `constant sheaf`, `K-injective`, `constant-ring`, `diagram-site`, `tower adjunction`, and `constant coefficient comparison`; none states the entire item. `same_as` remains the searched empty list.

## Review by Q88

I read the item's statement, its assigned chapter and unit, its blueprint ancestor in the current main-20261015 snapshot, and both versions of delivery-errors B--E. For the proof I read Stacks `sites.tex` Example 0H7J (constant sheaf and its universal property), `sites-modules.tex` 03D7 (module adjunction), 03DA (exact underlying abelian functor), 04JC (exact abelian inverse image), 03DI and 03DJ (localized module extension and exactness), `sites-cohomology.tex` 07A5 (Grothendieck module category), `injectives.tex` 079P (unbounded functorial K-injective resolution), and `derived.tex` 070H, 070Y, 070K and 0DVC (K-injectivity, total derived existence and canonical adjunction). I also read the pro-etale extension-by-zero definition 09AE and the statements of the existing localization/comparison nodes. No new nodes need separate source reviews. The source proof is not claimed to be a literal proof of the strict-tower specialization; `proof_origin.by` is `agent`.

Step 1 uses `lem-pur-proetale-constant-coefficient-comparison` for exactly its isomorphism assertion without finiteness. The other two cited definitions specify the actual adjunct and the constant sheaf's sheafification, respectively. The proof adds the coefficient, identity, and composition equations by evaluating their adjuncts on each constant section. It does not incorrectly extract naturality or compositional coherence from the isomorphism lemma alone. This also verifies that the specified comparison, rather than an arbitrary isomorphism, is used.

Step 2 takes the tensor-formula Hom bijection from `lem-weil-pbc-ringed-topoi-module-adjunction`, exact abelian inverse image from `lem-weil-pbc-site-pullback-abelian-exact`, and kernels/sheafified cokernels from `def-weil-sheaf-of-modules-category`. The hypothesis that the coefficient map is invertible is step 1; both ring sheaves are commutative. The balancing identity writes out why tensoring along this particular ring isomorphism just transports the action. The tower adjunction is proved by transposing its transition equations, and tower exactness by the kernel/cokernel universal properties. No non-elementary tower theorem is assumed.

Step 3 uses precisely the module equivalence, its exactness, and the product site given by `lem-weil-pbc-diagram-site-realization`. With the positive-integer opposite indexing category and the chosen pro-etale skeleton, both categories are small in the fixed universe. Thus the small-site hypothesis of `prop-pur-kinjective-resolutions-exist` is satisfied. That node states both Grothendieck abelianness and existence of resolutions; I did not cite a definition of Grothendieck abelianness in place of this result. Transfer of homotopies and acyclicity across an exact equivalence explains transfer of K-injectivity.

Step 4 is the elementary Hom calculation defining K-injectivity, with `def-pur-kinjective-complex` applied via the ringed diagram-site equivalences just established. Its exact-left-adjoint hypothesis was proved in step 2. The calculation tests an acyclic tower complex, not just a single level. In particular it makes no unsupported assertion that levelwise K-injective objects form a K-injective tower.

Step 5 uses `lem-weil-pbc-kinjective-total-derived` for total derived existence and computation on resolutions; step 3 supplies its required resolutions. The exactness required there is triangulated exactness of the homotopy functor, not abelian exactness of direct image: the proof writes out its preservation of the cone matrix, shifts, and homotopies. The two exact-functor nodes supply descent and the identification of that descent with the total left derived functor. The functor is derived on the strict tower category itself.

Step 6 uses `lem-pc-pre-derived-adjoint-functors-general` for its stated, functorial fraction-level Hom correspondence. The variables are typed as source `T_X`, target `T_Y`, right adjoint tower direct image and left adjoint tower inverse image. Everywhere-defined derived functors are already established by step 5. Setting the left resolution to the identity and using the right resolution gives the written unit and counit formulas. Thus the normalization is proved from the canonical correspondence, not from existence of some adjunction.

Step 7 uses all four clauses of `lem-weil-proetale-weakly-etale-localization` as applicable to an open immersion, including arbitrary-ring coefficient restriction; `lem-weil-pbc-proetale-ringed-open-comparison` identifies actual inverse image with the slice functor. The exact localized extension adjunction is exactly the conclusion of `lem-pur-site-restriction-module-adjunction-exact`. No quasi-compactness of the open or finiteness of coefficients is needed by these statements. The levelwise passage is the explicit argument already given in step 2.

Step 8 uses the same two exact-functor results and the canonical pre-derived adjunction theorem, now with both functors exact. Both identity resolutions are permissible, and the fraction formula reduces to the ordinary chain-map adjunction. This yields the termwise open unit and counit. It does not use a definition node as a theorem about open exactness.

I tested the hypotheses at the empty scheme, the zero ring, the identity map and identity open, and the empty open: the categories or maps reduce to the zero/identity ones and the Hom arguments still apply. An infinite ring such as the integers causes no finite-section argument anywhere. A tower with arbitrary zero or nonsurjective transitions still satisfies precisely the same naturality equations, so no Mittag-Leffler or transition-surjectivity hypothesis is hidden. An unbounded complex is handled through the cited unbounded K-injective theorem, with no truncation limit or uniform bound. All step texts are under 2000 characters. Every proof dependency has a verbatim statement quotation in `citations.json`; a traversal of their statement and proof dependencies found no path back to this item. No new clause-node, elementary-node, duplicate-node, or invented Mathlib leaf was introduced.

The five new Mathlib queries ran through the required msearch command, and their hits were read. The ordinary module pullback adjunction in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` (declarations around lines 60 and 79) proves only a constituent fact. The constant-sheaf file around line 158 even records the general pullback-commutation question as a TODO; its equivalence theorem has different hypotheses. The Grothendieck sheaf and condensed module search hits also omit the strict-tower unbounded adjunction and specified comparisons. None is an exact match or one-line specialization for the whole item. Existing inherited searches are preserved.
