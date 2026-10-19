# Stage-1 report: lem-coef-fixed-object-scat-left-proper

## Files written

- dag/nodes/sec-six-functors/lem-coef-fixed-object-scat-left-proper.json: statement, split; statement and statement dependencies unchanged. No exact Mathlib match. Eight explicit proof steps, using only existing lower-level nodes.
- citations.json: a verbatim statement quote for every node used by every step.
- No new nodes, no new Mathlib leaves, no unit changes, no Lean changes.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id, fixed-object terminology, left properness, SC_X, and simplicial-category terminology. There is no project declaration for the item. The few fixed-object hits concern tensor functors. The upstream master search was also empty for a relevant simplicial-category theorem; its sorry declarations were not treated as proofs.

## Sources wanted

WANTED: Dwyer–Kan, Simplicial localizations of categories, Sections 2.6–2.7, 7.3–7.6 and 8.2 (printed pp.270–271,277–279), for lem-coef-fixed-object-scat-left-proper. Read online at the Rochester PDF URL in the node, not downloaded or archived locally.

WANTED: Bergner, A model category structure on the category of simplicial categories, arXiv:math/0406507, Lemma 3.4, especially printed p.11 citing fixed-object properness, for lem-coef-fixed-object-scat-left-proper. Read online, not archived locally.

## What was wrong or needed attention

The imported statement is correct. Bergner's source uses fixed-object properness, referring to Dwyer–Kan 7.3; it does not itself prove left properness. Dwyer–Kan explicitly defers the nontrivial left-proper half to Section 8. Merely invoking properness or stability of trivial cofibrations would not split this item.

The natural existing citation lem-coef-fixed-object-simplicial-free-calculus cannot be used here: it has statement dependency lem-coef-coherent-nerve-comparison, whose proof uses lem-coef-simplicial-interval-cell-stability, whose proof uses this item. I checked that path in the actual dependency graph. I did not edit that existing node or create a duplicate. Instead steps 2–4 explicitly derive its needed coproduct assertion from the existing free-resolution augmentation, realization, diagonal, and Kan-model statements, all of which have no path back to this item. The remainder constructs and contracts the coproduct bar. This is an agent-written expansion of the source's contraction and comparison argument and is marked as such in proof_origin.

No statement dispute, no change to the unit's route, and no identification of different coefficient categories occurs. This is a foundational fixed-object model result in the existing ancestry of the coefficient-adjunction unit. I read the unit and chapter records and SETUP's three levels; this item is not the unit's key statement, so its realized fields are untouched. The current blueprint moves the ancestor to sk-thm-sf-package; the item has no blueprint_update. Its historical ancestry remains intact, and the relevant ancestor proof is the derived mapping-limit adjunction paragraph.

## Not duplicates

No new nodes were created. Whole-DAG searches covered fixed-object categories, properness, word filtrations, bar pushouts, and extra degeneracies. Whole-blueprint searches for left proper, free product, fixed object, two-sided bar and extra degeneracy found no alternative blueprint node stating this item. The free-calculus node overlaps a needed intermediate result but is not cited because that would make a cycle. Its lower inputs are reused, not duplicated as new statements.

## Review by Q88

I read Bergner Lemma 3.4, including the fixed-object properness sentence on printed p.11, and Dwyer–Kan 7.1–7.6 and 8.1–8.3, together with the free-product discussion in Section 2. I followed the source's fixed-object/free-extension and bar approach. The proof writes out the contraction omitted in Section 8.2; it never appeals to left properness while establishing that contraction. Since these papers are not local literature files, the origin is agent and the two archival requests are above. No SGA source is used.

For step 1 I opened lem-coef-simplicial-interval-lifting: its statement supplies exactly the fixed-object model structure and retracts of degreewise free extensions. The pushout computation is justified directly by its degreewise universal property, which also constructs the simplicial operators. The section and retraction under A are kept until the final step.

For step 2 I opened lem-coef-realization-finite-limits and lem-coef-kan-quillen-right-proper. The former states preservation of small colimits and finite limits in k-spaces; the latter defines weak homotopy equivalence by realization and supplies the model structure. I wrote the free-word normal form with identity old arrows allowed and proved the product/disjoint-union assertion by path components and based sphere maps. There is no hidden assumption that all simplicial categories are cofibrant. For step 3 the bisimplicial-diagonal node says exactly rowwise weak equivalences imply a diagonal weak equivalence, in either direction; no face-preserving free generators are assumed.

For step 4 I opened lem-coef-free-resolution-coproduct-augmentation. Unlike a bare counit theorem, its statement explicitly gives the augmentation AFTER coproduct with an arbitrary ordinary category, and says there is no freeness/cofibrancy hypothesis on either category. It therefore applies for each q to X_q,Z_q and X'_q,Z_q, not to an unproved enriched generalization. Step 3 supplies the other direction because every F^(p+1)Z_q is free. The cited diagonal theorem and the Kan model's two-out-of-three give the comparison for arbitrary factors. The augmentation squares commute by composing the nested words, not by choosing homotopy inverses.

Step 5 introduces the entire bar diagram, its face maps, its degeneracies (unused A factors inserted by the coproduct unit), and its augmentation. The simplicial identities are checked on factor inclusions, where they are associativity or insertion/deletion identities. This is a definition and a universal-property calculation, so it is the one elementary step and needs no auxiliary lemma node.

For step 6 I opened lem-coef-extra-degeneracy-contraction and checked all its displayed hypotheses. In a fixed q row the first factor decomposes as F_q*A_q, so there are n+1 labelled A copies. Inserting an unused copy BEFORE copy 0 gives h_n; it fixes F_q and V_q. At n=0, d_0 h_0 is the identity by folding the empty and old A copies, whereas d_1 h_0 sends the old A copy to V, precisely h_-1 after augmentation. For general n the other identities shift a factor label on both sides. Thus the node really supplies a simplicial section and homotopy, not just an additive chain contraction. The realization node turns that homotopy into a continuous one. The Kan definition then makes the augmentation a weak homotopy equivalence; no Kan complexes are required. The diagonal node applies to the natural augmentation even though the chosen contractions and F_q are not natural in q. This distinction prevents an invalid claim of a bisimplicial extra degeneracy.

For step 7 I checked that the two bars have the same A and free left extension, and only their final factors differ by the given weak equivalence u. At every bar degree the map is a finite coproduct of identities and u, exactly what steps 2–4 proved. Naturality at the last face uses that the source span has 1_A and the target span has u. The diagonal and Kan-model statements give the bottom canonical pushout map by the commuting augmentation square. Step 8 then constructs the pushout section/retraction by universal properties and uses retract closure from the same model structure. Every used node has a verbatim supporting quote in citations.json; the source's Proposition 7.3 itself is not used as an uncited lemma.

I tested O empty (vacuous mappingwise assertion), identity-only categories, x=y and loop generators, empty mapping sets, the zero-edge normal-form summand, and the first two degrees of the bar contraction. When A is identity-only, the inserted factors do nothing and the bar is constant as expected; when the free factor F is empty, it is the usual split bar of A acting on V. No nonempty mapping-set or fibrancy hypothesis enters. I checked B–E against the actual files: no new unsplit proof sketches, no new duplicate or item-clause nodes, no unperformed search records, no unintroduced new-node objects, no source tag standing for a missing theorem, no cyclic citation, and no off-unit replacement of the unit proof. No Stacks tag states this enriched-category theorem, so no false Stacks attribution has been introduced.

## Unfinished work

None for this one-level split. The existing lower-level unsplit nodes retain their own work. The second reader should inspect the explicit bar factor labels and the non-natural row contractions especially; these are written out to make that review possible. Delivery is intentionally left to that reader.

## Second reading by Q88

- Step 1 checked against `lem-coef-simplicial-interval-lifting`: the fixed-object model structure, free-extension retract, degreewise coproduct form, and pushout setup match the cited statement; verdict: pass.
- Step 2 checked against `lem-coef-realization-finite-limits` and `lem-coef-kan-quillen-right-proper`: the alternating-word decomposition, finite products/disjoint unions, and realization definition of weak equivalence justify coproduct invariance; verdict: pass.
- Step 3 checked against `lem-coef-bisimplicial-diagonal-equivalence`: the two simplicial directions and diagonal identification are correctly specified, including non-generator-preserving faces; verdict: pass.
- Step 4 checked against `lem-coef-free-resolution-coproduct-augmentation`, `lem-coef-bisimplicial-diagonal-equivalence`, and `lem-coef-kan-quillen-right-proper`: the free comonad augmentation applies to each ordinary degree without freeness assumptions, and the two diagonal comparisons plus two-out-of-three give arbitrary coproduct invariance; verdict: pass.
- Step 5 checked directly against the Dwyer--Kan Section 8.2 bar construction: all faces, degeneracies, augmentation, and simplicial identities are stated at the fixed object set; verdict: pass and elementary.
- Step 6 checked against `lem-coef-extra-degeneracy-contraction`, `lem-coef-realization-finite-limits`, `lem-coef-kan-quillen-right-proper`, and `lem-coef-bisimplicial-diagonal-equivalence`: the labelled A-factor contraction has the required extra-degeneracy identities, and realization and diagonal arguments apply without Kan hypotheses; verdict: pass.
- Step 7 checked against the two bar constructions and the cited diagonal/model statements: the map is identity on intermediate factors, uses `u` on the final factor, commutes with all operators, and two-out-of-three identifies the pushout arrow; verdict: pass.
- Step 8 checked against `lem-coef-kan-quillen-right-proper`: the pushout of the free-extension retract is an arrow-category retract, and retract closure gives the stated conclusion, including the empty-object-set case; verdict: pass.
- New nodes: none; there were no new statements requiring B1--B7 or duplicate/Mathlib-node removal checks.

Changes: in step 1 supplied the pushout construction that upgrades an arrow-category retract to a retract with domain A fixed, using the degreewise free-product form and ba=1 (C3); expanded step 6 into the explicit factor maps for every remaining face and degeneracy identity (E5); corrected the proof subpart pinpoints in steps 2 and 3 to Dwyer--Kan 2.7(i) and (ii); expanded citation quotes to include the weak-equivalence definition and every extra-degeneracy hypothesis. No statement or dependency changed, and no new nodes were needed. I verified the item statement against Bergner, Lemma 3.4 (printed p. 11), and Dwyer--Kan Sections 2.6--2.7, 7.3--7.6, and 8.2; checked the small cases of empty object set, identity-only categories, empty mapping sets, loops, and the first bar degrees; and found no statement, dependency, citation, cycle, or source-hypothesis defect.

Independent second-reader Mathlib search: LeanFinder query “The category of simplicial monoids with a fixed object set has weak equivalences preserved by cobase change along free extensions” returned eight hits about simplicial-set cofibrations and formal stability of (trivial) cofibrations; none states the fixed-object left-properness theorem. Its actual search record is appended to searches.jsonl and the item. The read-only source checkouts also have no fixed-object-left-properness declaration.
