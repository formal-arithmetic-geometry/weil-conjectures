# Worker report: lem-pc-coherent-supported-property-devissage

## Files written

- dag/nodes/sec-picard-framework/lem-pc-coherent-supported-property-devissage.json: split statement; four proof steps, no Mathlib match. Statement and statement dependencies retained.
- citations.json: nine step/node entries, each quote checked verbatim against the current cited statement.
- searches.jsonl: the prescribed tool's five actual search records for this item.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. No Lean or repository files were written and no compiler, Lake, build or local delivery check was run.

## Attachments

None. Searched WeilConjectures by the item tag, supported/devissage and coherent/devissage/property terminology. The coherent_property_devissage_integral_subschemes theorem has different hypotheses (generic witnesses and direct-sum descent), and the private support_integral_ideal fact in its file proves only a support identity, not this item. The other ideal-comparison files cover partial arguments. None is an exact attachment.

## WANTED

None: the needed Stacks sources and current blueprint are available locally.

## Corrections and source route

The statement is correct, including the explicit zero and isomorphism hypotheses, and was retained. The primary source was previously recorded as 01YH; its actual extension-only devissage is 01YG, lemma-property-initial, whose proof applies 01YF and propagates along a filtration. The support restriction is the refinement used in the first and final proof paragraphs of 01YH. I corrected the source metadata and wrote the support check rather than assuming the closed subschemes of the filtration lie in S.

Read the current latest blueprint lem-pc-coherent-hi statement and proof: this is the coherent support-devissage tool below the proper coherence/Noetherian-support-induction sentence. Read the chapter and sk-thm-picard-coherence unit; no chapter or unit route is changed. The current same-unit finite-presentation filtration drops nonzero/coherence clauses, so I used the existing stronger coherent filtration node as a generic tool and declared all off-unit statement uses in split_report.tool_uses. There are no new nodes, and no statement clauses were moved into substitute nodes.

## Searches and reuse

Whole-DAG searches by 01YF, 01YH, filtration/integral/ideal and coherent support found the existing filtration, exact-stalk, closed-pushforward-stalk, generic-ideal and closed-support results. blueprint_refs ancestor returned lem-pc-coherent-hi; searches for coherent filtration, 01YF and property of coherent returned no blueprint duplicate. The item keeps same_as empty. The source-library searches found no exact item declaration.

Ran the prescribed msearch command with two LeanFinder phrasings, LeanSearch, Loogle and grep. Read their returned hits. LeanFinder gives Noetherian predicates/instances and IdealSheafData; LeanSearch gives ideal zero-locus/support and subscheme constructors; Loogle gives isQuasicoherent_restrictFunctor; grep finds no devissage or coherent-filtration result. Read Mathlib AlgebraicGeometry/IdealSheaf/Basic.lean and Modules/Tilde.lean at that restriction declaration. In particular IdealSheafData.supportSet is the zero locus of the ideal, not the support of the ideal as a module (some search summaries misleadingly say otherwise). None states this theorem. Existing historical searches were retained; new entries reproduce precisely the five recorded query strings and tool names.

## Not duplicates

No new nodes were created. The item differs from the unrestricted two-out-of-three property theorem and from the higher-rank cohomological devissage theorem: it requires only extension closure on modules supported in an arbitrary subset, and assumes all nonzero ideal pushforwards there. Those stronger/different hypotheses were not silently interchanged.

## Review by Q38

I read coherent.tex, lemma-coherent-filter (01YF), lemma-property-initial (01YG), and the whole proof of lemma-property-irreducible (01YH), as well as the coherent-Noetherian equivalence (01XZ). I checked the supporting source statements in modules.tex (01AG with its preceding kernel/cokernel stalk formulas, and 01BY), sheaves.tex (00AE closed-pushforward stalks), and morphisms.tex (056J support closedness and 01T6 locally finite type over a locally Noetherian scheme). No SGA source is used.

Step 1 takes precisely the nonzero coherent ideal factors and coherent intermediate submodules asserted by lem-weil-pbc-coherent-filtration-integral-subschemes. Its hypotheses are satisfied because X is Noetherian and F coherent. lem-weil-pbc-coherent-modules-kernel-cokernel-sum explicitly makes the consecutive cokernels coherent. I opened both statements, rather than using a weaker finite-presentation filtration.

Step 2 uses lem-weil-pbc-module-stalk-exact, which explicitly gives injectivity of submodule stalk maps and the cokernel stalk quotient. For x outside S the ambient stalk is zero, so both the submodule stalks and their quotient stalks are zero. Stalk isomorphisms preserve zero modules. This is a short elementary inference from the cited formulas, with no closedness assumption on S.

Step 3 uses def-weil-closed-immersion for both its affine quotient description and its homeomorphism onto a closed image. Quotient algebras are generated as algebras by the empty family, so the closed immersion is locally of finite type; pqf-lem-locnoeth-lft then supplies the precise locally Noetherian hypothesis on Z. pqf-lem-coherent-ft-locnoeth now makes the coherent ideal quasi-coherent BEFORE applying lem-weil-pbc-integral-scheme-ideal-generic-stalk. That node explicitly gives nonzero generic stalk for a nonzero quasi-coherent ideal on an integral scheme. lem-weil-pbc-closed-pushforward-stalks identifies this stalk after pushforward and gives vanishing outside the closed image. The quotient Q is coherent on the locally Noetherian X, hence quasi-coherent of finite type by the same equivalence; lem-weil-pbc-finite-type-module-support-closed explicitly makes its support closed. Thus containing the generic point forces it to contain the whole closed image. This proves i(Z) is inside S, which is exactly the hypothesis needed for the item's ideal assumption. I added the locally Noetherian check on Z during self-review to avoid applying the generic-ideal node before quasi-coherence was justified. Every cited node's actual statement was opened and its verbatim quote is in citations.json.

Step 4 is finite induction, with base P(0), quotient P(Q_j) from Step 3 and extension closure applied only to the supported coherent terms established in Steps 1 and 2. Isomorphism invariance is used to transfer P from the ideal pushforward to Q_j. No reverse two-out-of-three implication or direct-summand hypothesis is used.

I checked the delivery-errors B--E cases: no new statement-only nodes are needed, no duplicate or elementary facts became nodes, each non-elementary input is cited, no proof of a cited node is being used in place of its statement, and no induction or dependency is circular. All proof steps are below 2000 characters. Small cases checked: X empty, S empty, F zero, filtration length zero and zero-dimensional integral factors. They use the explicit P(0) base; an arbitrary nonclosed S causes no issue because only the closed supports of actual factors must lie in it. Nonzero ideals are necessary for the support-equality argument; the filtration node supplies that clause, rather than silently deleting zero factors from a weaker statement. All references are existing generic tools and none depends on this item.

## Unfinished work

None in this stage-1 split. The cited unsplit or sorry-dependent nodes remain separate work items; this delivery claims no Lean proof.
