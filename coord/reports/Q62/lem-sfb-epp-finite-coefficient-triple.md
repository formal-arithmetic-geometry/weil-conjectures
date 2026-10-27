# Q62 stage-1 delivery: finite coefficient triple

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-finite-coefficient-triple.json`: item, split; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-artin-schreier-degree-p.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-complete-coefficient-field-arithmetic.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-mixed-finite-level-preparation.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-mixed-level-lowering.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-normal-base-branch-conjugacy.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-normal-ramification-filtration.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-purely-inseparable-degree-p.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-totally-ramified-base-change.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-weak-solution-descent.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.

`citations.json` contains a verbatim statement witness for every use of every proof step. `searches.jsonl` is the search command's actual log; `search_results.jsonl` retains its actual displayed hits. `dag_blueprint_searches.txt` records the whole-blueprint searches.

## Attachments

None. Searches of the live `lean/WeilConjectures/` for the blueprint tag, Epp, weak solution, and the new lemmas' concepts found no project declaration proving this item. The hits for substrings such as stepPullback are unrelated. No Lean was written and no compiler or build was run.

## WANTED

None. The required Stacks sources are present locally.

## Problems and corrections

The item is the complete-DVR special case of Stacks 09F8 with a further characteristic-p clause justified by the 09F9 observation about finite extensions of k((t)). Its statement needs no correction: zero versus one as the initial perfect-core exponent gives the same intersection, and its normalization definition is the source's weak-solution notion. No claim of arbitrary extension stability was added.

The source's filtration language calls degree-p Galois inertia steps totally ramified. For imperfect upper residue one must also allow index-one steps with inseparable residue; the new filtration statement therefore uses the broader degree-p Galois case, which both degree-p inputs actually handle. The tame case is allowed to have a separable residue extension rather than unchanged residue after base change. This is a harmless enlargement of the inductive claim, not a change to the item.

The source's induction moves from a solution on one branch to all conjugate branches rather tersely. I made the last coefficient extension normal over the original field before invoking conjugacy. Normal closures here can be taken separable over the intermediate coefficient field; that omitted structural assertion is an explicit new arithmetic input. Further extensions used in this argument are separable and totally ramified, precisely the extensions for which 09ER applies.

I initially included the uniformizer-root calculation in the new arithmetic input, then removed it after reading the existing `lem-sbc-dvr-uniformizer-root-algebra`. Step 3 now derives the finite-degree, normalization and ramification assertions directly from that statement, the monic quotient basis and PID normality. The mixed-level preparation and lowering nodes spell out their polynomial, valuation and level so that they are meaningful without reading their source tags. An invalid guessed finite-etale definition reference was removed; the filtration now states the needed ideal and separable-residue conditions explicitly.

## Unfinished work

Nothing in the assigned one-level split remains. The nine new nodes are deliberately statement-only and await their own stage-1 work; they are genuine structural facts or proper degree-p cases, not repetitions of the full arbitrary finite-extension existence claim. No new Mathlib leaves are asserted.

## Review by Q62

I read Stacks `more-algebra.tex`, the definition of weak solution in the eliminating-ramification section, all of 09F8 and its proof, and the 09F9 compositum paragraph. For the new nodes I read 09ES (normalized branch descent), 09EU (normal base-field action), 09ER (Eisenstein totally ramified base change), 09EY (all three purely inseparable alternatives), 09F1 (Artin-Schreier coefficient argument), 09F4 (Kummer finite-level preparation), 09F5 (its level definition and lowering proof), and 09EE/09EH (the inertia filtration and unramified invariant subfield). For the arithmetic node I checked the specific omitted normal-closure claim in the 09F8 induction and the Laurent-series observation of 09F9. For the root calculation I read 09EV and the existing root-algebra node rather than creating a duplicate. I read the current latest blueprint's direct-image proof (3), which no longer contains an Epp input; the item's inherited historical ancestry is reported honestly, including its null ancestor, and no chapter or unit files are changed.

Step-by-step C1/C4 check:

1. Complete finite normalization says both that the given dominating DVR is the integral closure and that it is complete; the filtration supplies the finite normal enlargement and tower, and descent (i) returns a solution to the original upper DVR. Each claim is in a cited statement.
2. This only states the induction and its length-zero case. The weak-solution tensor and ideal conditions at length zero are the original index-one equality.
3. The existing root-algebra statement gives the domain/DVR/maximal ideal; the monic quotient basis gives degree after localization; PID normality gives the integral-closure identification. The residue and index equalities and derivative separability test are written out. This is the short elementary calculation, not a new node.
4. The filtration's unramified case explicitly gives index one. In the tame case its separable-residue condition is used over V, exactly the base ring of the existing tame-cancellation statement; I do not silently assume separability of an arbitrary extension over k. Totally ramified base change applies to U→V because its index is one, and the root field has the required degree/index and unchanged residue by step 3. Tame cancellation is then applied to V→W and its root extension. These give both required index-one factors.
5. The purely inseparable input gives exactly its three alternatives. In its root alternative the reduced tensor has a unique root, the resulting DVR has the root as its maximal-ideal generator, and step 3 identifies its normalization. The other two alternatives immediately give the required ideal equality.
6. The Artin-Schreier input has the common complete DVR hypotheses, characteristic p, degree p Galois and the perfect-core equality. It provides a separable totally ramified solution; I use no unsupported assertion that a general separable coefficient extension preserves a weak solution.
7. Finite-level preparation either solves the mixed-characteristic case or gives the precise finite-level situation. Lowering gives the explicit bound, and the doubling-distance argument proves finite termination even though the rational denominators can change. At every repetition 09ER preserves the bottom index-one condition and upper residue, and complete normalization/arithmetic preserve completeness and residue k. Descent composes the constructed stages; its branchwise normalization clause is explicit, so a solution on one selected top branch is never treated as a solution on every branch. Every non-elementary comparison here is in the cited input statements.
8. Coefficient arithmetic supplies a normal enlargement separable over the first solution. Its total ramification is part of that same arithmetic statement; hence 09ER applies branchwise. The remaining branch tower is shorter by the filtration's explicit stability clause. Complete finite normalization provides finite residue extensions and complete DVRs; the existing finite-extension-perfect-core statement puts the new perfect core algebraically over k, and algebraic closedness gives equality. Thus induction has exactly its original hypotheses.
9. I normalize the final coefficient extension before conjugating. Arithmetic gives separability over H2, 09ER preserves solved branch indices, the explicit branchwise clause of descent composes the chosen stages, and 09EU's new branch-conjugacy statement applies to the original top DVR and the normal extension N2/F. The coefficient DVR's unique maximal ideal is invariant, so all branches have the same lower index, not just conjugate upper rings.
10. The arithmetic input writes the SAME solution field as a separable/uniformizer-root compositum for the arbitrarily specified t. No further base extension is used in this last step.

I opened every cited existing statement, including the complete-normalization, finite perfect-core, tame-cancellation, root-algebra, monic quotient and PID-normality nodes. Citations quote exactly their statements and do not borrow facts from their proofs. The cross-unit normalization/perfect-core and elementary algebra inputs are explicitly declared as generic tool uses. All new nodes introduce their own rings, fields, residue notation, reduced tensor products, and any weak-solution or level terminology they use, and carry exact source tags and the inherited blueprint place. None has a proof sketch or proof dependencies.

Edge cases checked: identity coefficient and upper extensions, length-zero towers, e=1 and n=1, purely inseparable root tensors with nilpotents removed, degree-p extensions of index one with inseparable residue, trivial branch factors deleted after base change, p=2 in the mixed polynomial, level zero, l approaching p, and r=0 in the prescribed compositum. A complete DVR is never silently treated as a field, the upper residue need not be perfect or finitely generated, and all lower residue extensions remain k because they are finite over algebraically closed k. No proof step exceeds 2000 characters. No prohibited SGA source is used.

Mathlib review: the semantic hits consist mainly of ordinary ramification/inertia degree formulas, unramified base change, purely inseparable exponents and perfectClosure, and Kummer/cyclotomic number-field statements. I read the nearby source of ramificationIdx, the Galois prime-transitivity instance, the normal-closure construction, and the perfectClosure intersection/compositum lemmas. The transitivity instance assumes a Galois invariant-ring action; supplying that action for a possibly inseparable normal coefficient extension on a reduced tensor algebra is exactly the missing work, so it is not a one-line Mathlib leaf. The generic unramified base-change theorem requires more than equality of maximal ideals and does not cover an inseparable or transcendental upper residue. No candidate states the finite Epp construction, finite-level inequality, or complete-DVR uniformizer compositum structure. Actual queries and full results are retained unchanged in the node records and search files.

## Not duplicates

lem-sfb-epp-complete-coefficient-field-arithmetic vs lem-sfb-epp-compatible-coefficient-dvrs: the new statement is coefficient-field arithmetic (total ramification, separable normal enlargement, and the specified uniformizer compositum), asserting no weak-solution existence; the existing statement instead provides Compatible coefficient DVRs for the complete Epp pair.

lem-sfb-epp-complete-coefficient-field-arithmetic vs lem-sfb-epp-finite-coefficient-triple: the new statement is coefficient-field arithmetic (total ramification, separable normal enlargement, and the specified uniformizer compositum), asserting no weak-solution existence; the existing statement instead provides Finite coefficient triple in Epp elimination.

lem-sfb-epp-complete-coefficient-field-arithmetic vs lem-sfb-epp-weak-perfect-residue: the new statement is coefficient-field arithmetic (total ramification, separable normal enlargement, and the specified uniformizer compositum), asserting no weak-solution existence; the existing statement instead provides Weak Epp over a perfect residue field.

lem-sfb-epp-complete-coefficient-field-arithmetic vs lem-sfb-epp-strict-complete-reduction: the new statement is coefficient-field arithmetic (total ramification, separable normal enlargement, and the specified uniformizer compositum), asserting no weak-solution existence; the existing statement instead provides Strict residue and completion reduction in the proof of Epp.

lem-sfb-epp-complete-coefficient-field-arithmetic vs lem-per-complete-dvr-finite-normalization: the new statement is coefficient-field arithmetic (total ramification, separable normal enlargement, and the specified uniformizer compositum), asserting no weak-solution existence; the existing statement instead provides Finite normalization of a complete discrete valuation ring.

lem-sfb-epp-normal-ramification-filtration vs lem-sfb-epp-compatible-coefficient-dvrs: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Compatible coefficient DVRs for the complete Epp pair.

lem-sfb-epp-normal-ramification-filtration vs lem-sfb-epp-finite-coefficient-triple: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Finite coefficient triple in Epp elimination.

lem-sfb-epp-normal-ramification-filtration vs lem-per-dvr-char-zero-tangent-kernel: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Finite-order residue-trivial DVR automorphisms in residue characteristic zero.

lem-sfb-epp-normal-ramification-filtration vs lem-per-complete-dvr-finite-normalization: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Finite normalization of a complete discrete valuation ring.

lem-sfb-epp-normal-ramification-filtration vs lem-exc-dvr-inertia-order-prime-part: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Prime-to-residue-characteristic part of finite inertia order.

lem-sfb-epp-normal-ramification-filtration vs lem-exc-finite-group-cauchy: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Cauchy's theorem for a finite field-automorphism group.

lem-sfb-epp-normal-ramification-filtration vs lem-exc-finite-dvr-tame-inertia: the new statement constructs a four-type finite normal tower and its branchwise base-change stability; the existing statement instead provides Finite discrete-valuation normalization and tame inertia character.

lem-sfb-epp-weak-solution-descent vs lem-sfb-epp-strict-complete-reduction: the new statement is descent and composition for arbitrary finite normalized coefficient towers, without a residue-perfectness assumption; the existing statement instead provides Strict residue and completion reduction in the proof of Epp.

