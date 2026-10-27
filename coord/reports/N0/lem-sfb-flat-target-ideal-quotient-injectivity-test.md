# Stage-1 report: lem-sfb-flat-target-ideal-quotient-injectivity-test

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-target-ideal-quotient-injectivity-test.json: existing statement, now split into six proof steps, statement unchanged. Mathlib verdict: no exact match or one-line specialization.
- citations.json: seven step/node entries quoting the complete cited statements verbatim, including their hypotheses.
- report.md: this report. searches.jsonl contains the actual search-command results; write_split.py records the initial assembly.

There are zero new DAG nodes and zero new Mathlib leaves. Every dependency is reused.

## Attachments

None. Searched the project under lean/WeilConjectures for the item id and for universal-injectivity, pure-monomorphism and quotient-injectivity terminology; the related algebra and scheme declarations do not state this module criterion. A declaration about universal injectivity of spectra is a different notion.

## Wanted

None. All sources needed here are in literature/stacks-project/algebra.tex.

## Errors and changes

The imported statement is correct and unchanged: arbitrary commutative R, arbitrary L, flat M, and tests modulo every finitely generated ideal. No flatness or finiteness assumption is added to L. The source's final filtered-colimit argument is implemented as its direct elementwise finite-sum argument: a relation v(l) in IM uses only finitely many coefficients, hence occurs in JM for a finitely generated J contained in I. This is a few-line step, not a new lemma node.

The source reduces to finite modules via Tag 058K. The reused DAG criterion lem-trf-universal-injective-finite-test states finitely presented tensor tests over arbitrary rings and finite-module tests only over Noetherian rings. The proof therefore explicitly starts with finitely presented Q, obtains finite generators from its finite presentation, and applies only the first equivalence. This prevents an accidental Noetherian assumption or misquotation of the reused criterion.

The direct cyclic filtration by spans of the generators, its R/I identification, tensor quotient identification, and diagram chase are written out as elementary steps. Right exactness is an explicit non-elementary citation, rather than being attributed to the definition of flatness. There is no new node restating a clause of the item.

The current blueprint was read in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, especially det-thm-sf-ctf-stability-direct-images proof (3). This is an auxiliary algebra lemma below the inherited BLR S-density route recorded in the item's via list; it does not change a unit's theorem or proof route. blueprint_refs.py ancestor reports None for the existing chain, so the existing null from.node and via list are retained. Searches of the whole DAG by Tag 0AS5 and of the imported blueprint by universal injectivity and ideal quotient found no duplicate blueprint theorem; same_as remains empty.

## Not duplicates

No new nodes were created. The existing tensor-right-exactness lemma and finitely-presented universal-injectivity criterion are cited rather than duplicated. The criterion for flatness in Mathlib tests ideal inclusions tensored with a fixed module and is not this criterion for an arbitrary map L to M.

## Mathlib searches

Preserved the item's historical search records and appended only the searches actually run for N0 in searches.jsonl: LeanFinder in two phrasings, LeanSearch, Loogle with Module.Flat and Function.Injective, and grep in RingTheory/Flat. Read the returned signatures and the local source of Module.Flat.iff_rTensor_injective, iff_rTensor_injective', and rTensor_preserves_injective_linearMap. They characterize flatness of one tensor factor or preserve injectivity when tensoring with a flat factor. They do not turn reduction-modulo-ideal injectivity of an arbitrary map into universal injectivity in one line. Thus the item is split, not a Mathlib leaf. No service failure was recorded as absence.

## Review by N0

I read Tag 0AS5 (lemma-check-universally-injective-into-flat) in algebra.tex, its cyclic-filtration source Tag 00KZ (lemma-trivial-filter-finite-module), the exactness source Tag 00DF (lemma-tensor-product-exact), the definition-flat paragraph Tag 00HB, and the finitely presented test clause of Tag 058K (theorem-universally-exact-criteria). I read the statement of each dependency in its DAG file and checked what each step actually takes from it. There are no new node sources to review.

Step 1 uses only def-weil-pbc-module-tensor-product: its bilinear universal property gives the factor swap and the quotient maps, and its assertion that pure tensors generate verifies the two inverse composites. I checked that the inverse kills IX and that the naturality formula is av(l) modulo IM; the quotient is by IX, not by an ideal in a different ring.

Step 2 uses the isomorphism already proved in Step 1 and the stated hypothesis (ii), with no outside theorem. An element of IM is a finite sum by the inline definition in the item's statement. J is generated by precisely those coefficients, so it is finitely generated even if I is not. J=0 handles the empty sum. This replaces the source's colimit notation with the actual finite witness used in the argument.

Step 3 uses the exact finite presentation in def-sc-finitely-presented-module to choose a finite generating list. I checked I_i is an ideal, the displayed map R/I_i to Q_i/Q_(i-1) is bijective by its stated kernel and generating description, and that no I_i need be finitely generated. This is an explicit elementary construction, not an application of an uncited filtration theorem.

Step 4 uses the full right-exact tensor rows stated by lem-weil-pbc-tensor-right-exact, whose hypotheses hold because Q_(i-1) is a submodule of Q_i and C_i is its quotient. It separately uses def-weil-pbc-flat-ring-map only for the injection Q_(i-1) tensor M to Q_i tensor M. This definition explicitly states preservation of injectivity; it is not asked to supply right exactness. Tensor naturality is checked on generators using def-weil-pbc-module-tensor-product. No injection of Q_(i-1) tensor L into Q_i tensor L is asserted or needed.

Step 5 is the elementary diagram chase through those rows, with the induction claim, zero base, and induction step all explicit. The upper-row exactness lifts z to y; only the lower-row left map is required injective. Thus the argument never assumes L flat. Step 6 applies precisely the arbitrary-ring, finitely-presented-test equivalence in lem-trf-universal-injective-finite-test. It does not use that node's separate Noetherian clause. I declared this generic off-unit tool in split_report.tool_uses; the module-theoretic test criterion is not provided by the unit's direct-image lemmas.

I checked small cases: R the zero ring, Q=0 (empty generating list), J=0 (which detects injectivity of v itself), J=R (both quotients zero), L=0, and M=0. For M=0, condition (ii) at J=0 forces L=0, as required. For the familiar nonsplit injective map 2:Z to Z, the J=(2) test fails, agreeing with failure of universal injectivity after tensoring with Z/2. All proof steps are shorter than 2000 characters, and the quotient identifications and kernel chase have their formulas rather than concealed comparison lemmas. I corrected my working reference for the elementary filtration to the verified tag 00KZ. No statement dispute or uncompleted mathematical obligation remains.

## Unfinished work

None for this stage-1 item. The maintainer's independent review and downstream formalization remain the normal subsequent stages.
