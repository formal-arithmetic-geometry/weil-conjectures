# Stage-1 delivery: lem-sfb-injective-pushforward-totally-acyclic

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-injective-pushforward-totally-acyclic.json: statement, split; no Mathlib match. The statement and statement dependencies are unchanged. Five proof steps reuse existing nodes. No new nodes, no new Mathlib leaves.
- citations.json: eleven step/node entries, each quoting the actual cited statement verbatim. The launcher consumes this supporting file.
- report.md: this report. searches.jsonl is the search command's own log, not hand-written evidence.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, total acyclicity, limp, and injective pushforward. The exact tag is absent. TopCat.Sheaf.injective_pushforwardAb_obj (Topology/Sheaves/PushforwardCohomology.lean:58) concerns abelian sheaves on topological spaces. The scheme-module Čech and ordinary evaluation declarations concern site objects or opens. None covers arbitrary ringed topoi and all sheaves of sets without flatness. These narrower declarations do not justify ATTACH.

## WANTED

None. All sources used are in literature/stacks-project/. No SGA source is used.

## Corrections and route

The item was an unsplit statement, not a proof. Its statement is the module-cohomology interpretation of Stacks 072Z, with the definition from section-limp and 072Y written inline. No statement dispute was found. Its explicit warning about nonflat structural ring maps is essential: restriction of scalars need not preserve module injectivity, so the abelian-sheaf preservation-of-injectives argument cannot replace this proof.

The proof uses the existing ringed-site object-evaluation case, not a new node restating total acyclicity. An arbitrary K is handled by its element-site slice; there restriction has an exact left adjoint. The ordinary slice direct-image identity then lets the existing site-presentation and site-object acyclicity statements apply. The site-presentation statement in the DAG contains clauses (1)-(6) of 03CR but omits clause (7), the ability to prescribe extra representables. I deliberately do not take clause (7) from it. Instead the slice reduction uses the separately stated exact localization theorem, then evaluates at the final object of the finite-limit replacement site. This repairs a possible C4 gap without creating a duplicate presentation node.

Read the current latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3), and the chapter and inherited unit records. This generic acyclicity input supports the inherited relative-Leray branch; it changes none of the unit or chapter route. The blueprint ancestor command returns None for the inherited created-item chain, exactly as its existing from.node records. The item retains that provenance and its precise inherited from.place. Whole-blueprint searches for total acyclicity, 03CR, larger sites, injective evaluation and the ordinary slice square found no blueprint node stating this item. same_as remains [].

## Existing inputs, not duplicates

There are no new nodes, so no new/existing duplicate pairs require resolution. The existing lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic assumes a continuous functor between the presented sites and concludes vanishing only at site objects. The item removes that presentation hypothesis and proves vanishing at every sheaf of sets. The difference is proved by the slice and equivalence steps. The global-acyclic sibling is only the K=1 consequence and is not used, avoiding a cycle.

## Mathlib searches

Retained the existing recorded searches, and appended the actual Q79 msearch queries from searches.jsonl: LeanFinder in two phrasings, Loogle with SheafOfModules and rightDerived, LeanSearch on derived sections over arbitrary sheaves, and grep in CategoryTheory and Algebra/Category/ModuleCat. Services answered successfully. Read the returned types: locally injective morphisms are not injective objects; sectionsFunctor is underived; K-injective and derived-vanishing results require an injective argument, which f_*I need not be. The final focused grep located Functor.isZero_rightDerived_obj_injective_succ at RightDerived.lean:153, again only vanishing at an injective input. This does not specialize in one line to the item. No Mathlib match was found.

## Tool uses

The split_report declares the off-unit statements as generic tools: enough injectives for module categories, exact arbitrary-sheaf localization, the ordinary localized module square, presentation by ringed sites, exact equivalence transport and the existing site-object acyclicity case. These supply prerequisites, not an alternative constructibility or alteration route. The current unit has no statements providing these generic site-theoretic tools.

## Review by Q79

I read sites-cohomology.tex section-limp (the definition of H^q(K,N)), 072Y definition-limp, and all of 072Z lemma-direct-image-injective-sheaf, including the distinction from flat pushforward immediately after it. I also read sites-modules.tex 03CR lemma-morphism-ringed-topoi-comes-from-morphism-ringed-sites, 04IE lemma-localize-ringed-topos, and 04IF lemma-localize-morphism-ringed-topoi. The statement agrees with 072Z: an arbitrary ringed-topos morphism, injective source module, every target sheaf of sets, all positive degrees. The module definition of H^q is explicit, so no unstated comparison to abelian-sheaf cohomology is used. There are no new statements to check against additional sources.

For step 1, I opened the statements of lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives. The first is for any small site and arbitrary ring sheaf, hence covers the commutative rings here; the second supplies precisely enough injectives. The element-site and presentation statements explicitly give small sites, which is why all these applications satisfy the size hypotheses. Step 1 cites those two statements only for that size assertion.

For step 2, I opened lem-weil-pbc-ringed-sheaf-slice-adjunction: it gives the pairs (U,s), the formula r_K N(U,s)=N(U), exactness of restriction and its exact additive left adjoint. I wrote out the lifting proof that restriction preserves injectives instead of pretending its statement already asserted that consequence. def-sp-injective-resolutions states exactly the extension property used. The compatible-section family is literally the natural map K to the underlying sheaf; pointwise addition agrees. Applying restriction to the same injective resolution proves equality of the section complexes. These are elementary consequences of the cited formulas and lifting definition, with no acyclic-resolution theorem hidden in the step.

For step 3, I opened lem-sbc-ringed-sheaf-slice-ordinary-square. It asserts the ringed slice morphism for every target sheaf A, and the module isomorphism r_Y f_* = f_{A*} r_X, with the restricted structural ring map. Set A=K and apply it to I. It does not assert derived comparisons, and none are used. Injectivity of r_B I is already proved in step 2. No identification of noninvertible coefficient maps with isomorphisms occurs.

For step 4, I opened lem-weil-pbc-ringed-topos-site-presentation and lem-weil-pbc-ringed-presentation-transport. The former gives the small finite-limit sites, continuous finite-limit-preserving functor and ringed commutative square. The latter explicitly states an exact equivalence of module categories, which is the only part used. Its stronger internal-Hom and local-completeness conclusions are not used. I checked source and target directions: J is on the source slice, J'=g_*J is on C', and e_*f_{K*}J is h_*J' on D'. Exact equivalence preserves monomorphisms and the lifting property, hence injectives; applying it termwise preserves the entire injective resolution. Terminal sheaves and full faithfulness identify global-section abelian groups, including addition. The module comparison follows from the ringed square and the induced module direct-image definition, whose scalar-action clause I also opened. This is a single routine equivalence argument, not an assumed cohomology comparison.

For step 5, I opened the full statement of lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic, not its proof. It has exactly the needed continuous site-functor hypothesis, enough injectives, common-universe size and no-flatness conclusion. The finite-limit replacement target site has a final object T, whose representable is the terminal sheaf without any subcanonical-topology assumption. Evaluation at T therefore is global sections. Apply that existing theorem to h,J' and T. This yields the positive-degree vanishing on the replacement slice, and the previously established equalities identify it with H^q(K,f_*I). No step uses this item's own conclusion. I checked the transitive dependency closures of the presentation, slice, ordinary-square, transport and evaluation inputs: none reaches this item, so this assembly introduces no cycle.

I checked delivery-errors B through E against the written files. No new nodes contain hidden proofs or duplicate clauses; citations quote statements rather than their proofs; no flatness or original-site presentation hypothesis is added. All five steps are below 2000 characters. Edge cases: f=id reduces to injective acyclicity for Gamma(K,-); K=0 gives the zero section functor and empty slice; K=1 gives ordinary global acyclicity; I=0 gives zero throughout. On the point with the nonflat ring map Z to F_p and injective F_p-module F_p, the pushed-forward Z-module is not injective but Gamma(K,-) is a product over the set K and is exact, so the stated vanishing is consistent and the proof never invokes the false injectivity claim. Infinite K is handled in the common coefficient universe; the element-site smallness statement supplies exactly that case. q=0 is deliberately excluded, and no vanishing there is asserted.

There was no earlier delivery in the sandbox and no return entry to repair. The substantive correction made while reviewing was to avoid borrowing the omitted prescribed-representables clause of 03CR from the existing presentation node: exact localization makes that clause unnecessary. citations.json contains the verbatim cited statements for every step/node pair.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled. The required server checks and delivery are run after this report is written; their outputs determine whether the delivery is accepted.
