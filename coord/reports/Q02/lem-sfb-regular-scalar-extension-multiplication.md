## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-regular-scalar-extension-multiplication.json: existing statement, now split into seven steps; no whole-item Mathlib match.
- citations.json: verbatim statements for all 21 step citations.
- report.md: this report.

No new nodes and no new Mathlib leaves. The existing leaf lem-sfb-mixed-bimodule-right-unitor supplies the general right-unit isomorphism. The sandbox also retains searches.jsonl and the local writing script as research artifacts; neither changes the repository.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag and for regular scalar extension, multiplication, regular modules and extension unitors. CategoryTheory/ModuleObjects/ExtendScalars.lean supplies the extension coequalizer and general descent/unit apparatus, but no declaration there states all the normalized regular-module, unit and global-multiplication clauses of this item. DerivedExtendScalars.lean and Sites/FlatExtendScalars.lean do not supply that complete statement either. No sorry declaration was treated as a finished proof.

## WANTED

None.

## Findings and changes

The imported item had no proof. Its statement is correct and is unchanged. Its blueprint ancestry already names the final sentence of det-def-sfb-constructible-local-model, through lem-sfb-coefficient-sections-localization and the supplementary nonconstant-section counterexample. I retain this ancestry, chapter and unit. This is not the unit's key node, so there is no unit-record edit.

I read the current main-20261015 extension definition and proof, the sheaf-tensor section and tensor-structure proof, the finite-constant-local-model statement and proof, and the corresponding DAG statements. The argument follows the balancing construction, using the existing mixed right-unitor leaf rather than creating a new node for a clause of the item. The unit clause and conjugation clause are computed explicitly in the item. The proof is marked agent-written because the blueprint does not itself give this complete specialization.

I searched the whole DAG for regular modules, scalar extension, sheafified tensor generators, and rightUnitorBimod, and used blueprint_refs.py ancestor and searches for regular scalar, scalar extension, regular module, regular and coequalizer. None of the blueprint statements states this complete item. Existing normalization-related nodes were read: lem-sfb-mixed-bimodule-right-unitor, lem-sfb-bimod-monoidal, lem-sfb-internal-scalar-extension-finite-presentation and lem-sfb-scalar-matrix-inverse-image. The first supplies the exact general tool; the others either treat different modules or assume a geometric inverse image. No duplicate node was introduced.

The logged Mathlib searches try two natural-language phrasings, two regular/tensor patterns and the actual bimodule-unitor name. LeanSearch, LeanFinder, Loogle and grep all answered. Loogle's failed CategoryTheory.Bimod.rightUnitor query was an unknown-name result, not evidence that there is no unitor: Bimod.rightUnitorBimod succeeds. I read Mathlib/CategoryTheory/Monoidal/Bimod.lean:685-690,717-737,764-770, including both concrete maps and the left-action compatibility. The grep limited to that single file prints oddly parsed file/line fields; its recorded output is retained as returned, and the source was read independently. The ordinary-module tensor-unit hits and sheafification scalar-action hits do not state the entire internal-sheaf normalization and conjugation. I reuse the existing right-unitor leaf and keep the actual sheaf comparisons in the proof.

## Review by Q02

I checked delivery-errors.md B through E against the node and the sources, rather than treating the imported dependency list as a proof. There are no new statement-only nodes to check for self-containment or unlogged searches, no repeated clause hidden as a new lemma, and no source-route replacement. The existing item's hypotheses and statement dependencies remain intact. Every proof step is below 2000 characters. The non-elementary tools are cited by their statements, and the routine computations explicitly give their maps or equations.

Step 1 uses the colimit preservation expressly stated in sk-def-sfb-sheaf-tensor. To avoid silently assuming a special theorem about the site, it constructs every coequalizer by the objectwise quotient of the difference and the universal property in def-weil-pbc-sheafification. The quotient has induced restrictions because f and g are natural. The small parallel-pair colimit of def-weil-pbc-category-colimit supplies exactly uniqueness of factorization, from which the proof writes out cancellation. This avoids citing a definition as an unproved general epi theorem. Only a finite indexing category is used.

Step 2 uses the two actual arrows, actions and functor definition stated in def-sfb-modobj-extension, together with the regular action from sk-def-sfb-module-objects. The three displayed action identities follow from the associative/unit and ring-morphism axioms explicitly stated in sk-def-sfb-ring-object. In particular this checks the mixed S-R-bimodule hypotheses, not merely an R-R case.

Step 3 uses the full statement of lem-sfb-mixed-bimodule-right-unitor: it allows different S and R, specifies these same two coequalizer arrows, specifies the left action through the first factor, and states both q pi = r and its unit-insertion inverse. These are the precise assertions needed here. The coequalizer representative comparison is written using the uniqueness clause of def-weil-pbc-category-colimit; its compatibility with the action is checked after the preserved tensor of the projection. The existence and tensor-preservation hypotheses were established in step 1. Forgetting the right action retains the claimed S-linear isomorphism.

Step 4 uses the natural generator maps and Hom bijections actually in lem-sfb-braided-sheaf-tensor-generators, and the right-unitor equation actually in lem-sfb-sheaf-tensor-unit-comparison. I checked their small-site/size hypotheses against the item's essentially small site and allowed coefficient universe: the generator node explicitly permits passage to a small skeleton. Ab is the stated closed symmetric example; its tensor is additive. The resulting formulas evaluate the structure maps of sk-def-sfb-ring-object. They apply after the presheaf tensor map, with no inference that all tensor-sheaf sections are pure tensors. The two comparison lemmas are declared generic tool uses in split_report: the constructible-local-model unit does not itself provide these arbitrary-site sheaf tensor comparisons.

Step 5 computes q iota with the ring-object left unit law and the actual unit insertion into def-sfb-modobj-extension. No evaluation on a nonexistent terminal object is used, and no unsupported identity of sectionwise relative tensor products is used.

Step 6 identifies compatible families with maps from the tensor unit using the unit Hom bijection of lem-sfb-braided-sheaf-tensor-generators, not an assumption that the site has a final object. It constructs m_t by multiplication, checks restriction compatibility, and writes the R-linear morphism equation of sk-def-sfb-module-objects. Commutativity of R is used exactly in t(ab)=a(tb); the same construction for S is legitimate because S is also commutative. Thus extension of scalars is applied to a genuine module morphism.

Step 7 uses the induced-map equation expressly specified in def-sfb-modobj-extension. It writes both composites before cancelling the projection and checks b phi(ta)=phi(t)b phi(a), using the ring-morphism axioms and commutativity of S. Equality on the ordinary presheaf tensor generators is promoted to equality of sheaf maps by the exact Hom-bijection statement of the generator node. Uniqueness of the parallel-pair colimit then cancels pi. This checks the asserted conjugation itself rather than citing an ordinary-module theorem as if it concerned internal sheaves.

I tested identity scalar change, the map Z to Z/n (nonflat for n>1), zero target ring, t=0, t=1 and nonunit t. All formulas use only the ring laws and the balancing relation; none uses injectivity, invertibility or flatness. For the empty site the only sheaf and all its maps give the same identities. For a site without a final object the compatible-family definition and the unit Hom bijection still apply. No ring-object or module-category equivalence with a different coefficient category is assumed. The construction also explains why noncommutativity would be a problem for the linearity check; the required commutativity is present.

## Not duplicates

No new nodes.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own stage states. This delivery contains no Lean changes or compiler activity.
