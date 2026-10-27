# Stage-1 delivery: lem-coef-derived-sections-scalar-coherence

## Files written

- dag/nodes/sec-six-functors/lem-coef-derived-sections-scalar-coherence.json — statement, split in seven steps; not a Mathlib leaf. Statement, statement dependencies, provenance, and all inherited Mathlib search records are preserved.
- citations.json — one verbatim statement quotation for every node cited in every proof step.
- report.md — this report. searches.jsonl is the unmodified output log of msearch.py. build_split.py is sandbox-only preparation material.

No new nodes; no new Mathlib leaves. No unit record is changed: this item is a descendant supporting the unit, not its key statement.

## Attachments

None. I searched the live WeilConjectures source for the blueprint tag, derived-global-sections/scalar terminology, and restriction/derived-global-sections combinations. No declaration states the complete item for arbitrary ring sheaves on an arbitrary small site. In particular, RightDerivedFunctor/MapDerivedComp.lean gives an exact-precomposition comparison only under PreservesKInjectiveComplexes. That additional assumption is absent here. RightDerivedFunctor/MapDerivedCategory.lean proves exact-functor descent, which supports only the elementary descent part, not the global-sections assertion.

## WANTED

None. The sources used are available locally.

## Corrections and inherited issues

No STATEMENT-DISPUTED issue or statement correction. The imported item had no proof. I supplied the argument without claiming that restricting an S-K-injective complex makes it R-K-injective. The essential quasi-isomorphism Gamma(j) is taken from the statement of the existing unbounded ringed-topos composition lemma, not from exactness of restriction and not from an uncited acyclicity assertion.

The cited generic tools in split_report.tool_uses are the restriction/direct-image identification, singleton-site module equivalence, and unbounded ringed-topos composition theorem. The unit's mapping-complex route does not itself provide these general tools. The current blueprint ancestor's proof paragraph 2, first and last mapping-complex comparisons, is preserved. Its current main-20261015 proof was read at sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md; the DAG retains the inherited unit assignment sk-prop-sf-biduality-general. No source from the prohibited SGA route is used.

## Mathlib and duplicate searches

I ran msearch.py with the item's own id, using LeanFinder, Loogle, grep and LeanSearch, then a second natural-language formulation in LeanFinder. All five queries and returned hits are in searches.jsonl and appended verbatim in the item's mathlib_searches. Loogle and grep returned no hits. Semantic hits included underived SheafOfModules unitHomEquiv and pushforwardSections maps, sheafification comparisons, and CategoryTheory.Sheaf.H/cohomologyPresheaf. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean, CategoryTheory/Sites/GlobalSections.lean, and CategoryTheory/Sites/SheafCohomology/Basic.lean: these supply underived maps or nonnegative Ext-valued cohomology of abelian sheaves, not the required unbounded coefficient comparison with its unit cocycle. No search service was unavailable. The inherited earlier searches are retained as inherited records, not represented as new searches by NU.

Whole-DAG and whole-blueprint searches included the scalar-restriction concepts, derived global sections, universal right derivation, Tag 0D6E, and the sheafification/global-sections construction. blueprint_refs.py ancestor reports prop-coef-integral-exceptional-adjoint; searches for derived global sections, restriction of scalars, right derived functor, global sections morphism, constant-sheaf functor, and 0D6E found no blueprint statement equivalent to this full unit-normalized scalar comparison. Existing statements provide every generic input, so same_as is empty and no node was created.

## Not duplicates

No new nodes. In particular I reused lem-weil-pbc-sheafification-sets-exact rather than creating a constant-sheaf finite-limit lemma, and reused the existing 0D6E node rather than creating scalar-comparison or scalar-cocycle clause nodes. Identity and cocycle are calculations inside the item.

## Review by NU

I read the worker brief, stage-1 contract, the three blueprint levels in SETUP.md, GOAL.md, the chapter and assigned unit records, and delivery-errors.md B through E (including the duplicated historical sections). I checked the mathematical source in sites-cohomology.tex, Tag 0D6E, lemma-derived-pushforward-composition: it proves unbounded composition via derived adjunction and pullback composition. For the global morphism I read sites.tex Tag 0H7J, example-constant-sheaf, its explicit Hom adjunction; Tag 06UN, definition-global-sections, which works even without a terminal site object; and Tag 00WJ, lemma-sheafification-exact, giving finite-limit preservation. There are no new-node sources to audit.

I opened and read the statement of every proof citation. For step 1, def-pc-sheaf-restrict-scalars says the abelian sheaf and arrows are unchanged, def-weil-sheaf-of-modules-category explicitly gives sectionwise kernels and sheafified cokernels, def-weil-abstract-derived-category gives localization, and def-sfb-right-derived-functor gives exactly the universal bijection. This justifies exact descent and its identity-unit normalization in a few lines, without an extra exact-functor node.

For step 2, the sheafification definition supplies the factorization adjunction, the constant-sheaf definition identifies the sheafified constant presheaf, and lem-weil-pbc-sheafification-sets-exact says finite limits are preserved for SET-valued sheafification. I deliberately did not cite the abelian-only exactness theorem for that assertion. The ringed-topos definition asks for precisely that left exact adjunction and a structural ring map. The displayed n times 1 construction supplies the latter. This is a direct construction and adjunction calculation, rather than a hidden new existence lemma.

For step 3, lem-weil-pbc-restriction-ringed-topos-module-direct-image has the correct contravariant ring orientation: a:R to S gives f:(Sh(C),S) to (Sh(C),R). The ringed-topos definition describes its module action. The singleton-site comparison explicitly gives an exact equivalence on modules and on derived categories. The existing composition node states BOTH a canonical natural isomorphism and the exact extra clause that g_*j is a quasi-isomorphism for K-injective source and K-injective target resolution. Its small-site hypotheses hold for the given site and for the singleton site. I verified the structural map of g_R f is the one of g_S by a(n1_R)=n1_S. No claim about intermediate K-injectivity is used.

For step 4, def-sfb-right-derived-functor states a bijection for every target functor G; taking G=H_R r has the correct source D(S) and target D(Ab). The underived family eta_R is natural and therefore has one unique preimage. This establishes the requested comparison on every complex, not merely at resolutions.

For step 5, prop-pur-kinjective-resolutions-exist supplies resolutions for arbitrary unbounded complexes on a site small in the coefficient universe. def-sfb-right-derived-functor says exactly that eta is invertible on K-injective complexes. Naturality at j has the order H_R(Qj) eta_R=eta_R Gamma(j); solving it gives the formula written in the proof. The composition node supplies invertibility of Gamma(j). Naturality at an S-K-injective resolution s then proves invertibility at every derived object. This is an argument using previously cited statements, not a new node restating the desired isomorphism.

For step 6, I checked both resolution identifications and their directions. The source map QGamma(L) to H_S(QL) is eta_{S,L}; the target map H_R(QrL) to QGamma(K) is eta_{R,K}^{-1} H_R(Qj). Under these the composition comparison is Gamma(j), hence agrees with the explicit sigma formula. Equality on all objects follows by naturality at invertible Qs and existence of complex representatives. Thus the claimed canonical comparison and its representative formula are proved, rather than inferred from existence of an unspecified isomorphism.

For step 7, I wrote both unit substitutions: the composite sends eta_T first to eta_S at r_ST M and then to eta_R at r_RS r_ST M. The scalar-action identity from step 1 identifies this with the unit defining sigma_RT. Injectivity of the universal bijection gives equality of natural transformations. The identity case is the same bijection applied to the identity transformation. There is no appeal to an unproved abstract coherence statement.

I checked zero complexes, the identity ring map, an empty site, and zero-ring coefficients. None requires a terminal site object or nonzero ring. The nonflat maps Z to Z/2 and Z to Z/4 to Z/2 are allowed: even the one-term complex Z/2 is injective over Z/2 but need not be injective over Z, so preservation of injectives would be a false shortcut. The proof instead chooses j and invokes exactly the 0D6E clause. No boundedness, flatness or extra acyclicity hypothesis entered. All seven steps are below 2000 characters; their elementary steps are explicit definition/universal-property or naturality calculations, and the substantive comparison theorem is a cited existing node. No proof clause has been moved into a fresh node, and no new dependency points back to the item.

## Unfinished work

None in this stage-1 split. The server dry run and delivery are the remaining procedural checks at the time this report is written.
