## Worker report

Item: lem-per-mixed-reduced-special-fibre-cover. Group Q83. Stage 1 only, 2026-10-19.

### Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-mixed-reduced-special-fibre-cover.json: retained the current statement, source and blueprint ancestry; supplied ten proof steps, their dependencies and specific tool-use explanations. No Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-epp-perfect-core-complete-local.json: new statement-only lemma, unsplit. No Mathlib match: complete-local fraction-field Epp property relative to a specified perfect subfield.
- dag/nodes/sec-deligne-laumon-a1/lem-per-epp-finite-family-traits.json: new statement-only lemma, unsplit. No Mathlib match: simultaneous normalized Epp base change for a finite family of excellent, possibly noncomplete upper traits.
- citations.json: retained 37 verbatim statement quotations and checked every one against the current node statement. It covers every node in every step's uses.
- report.md: this report. Existing searches.jsonl and research files were retained; no searches were invented or rerun merely because the preceding attempt failed to answer.

### Attachments

None. Searched the exact item and new-node tags in WeilConjectures/ in slopmaster2 and master, and searched slopmaster2 by Epp, Cohen, perfect subfield, elimination of ramification and reduced special fibre. The hits concerned ordinary geometric reducedness, slicing flat morphisms and component generalization, not this finite normalized Epp construction. Master is reference material only. There is no complete declaration to attach.

### Wanted literature

None. The ILO PDF is available, as are the Stacks sources. No SGA source is used.

### Audit and retained work

The earlier attempt left the split, two new nodes, 37 quotations, search log and a saved ILO text, but no report. I compared the item against the current repository: its statement, source, statement dependencies, creation metadata and blueprint fields agree; the repository item is unsplit with no reviewed record. I retained the proof and citations. Before writing this report, the authorized server srvcheck commands returned review_split PASS and check_dag OK with no introduced finding. Those are preliminary checks; the full deliver.py dry run follows this report.

I read ILO Expose IV 3.1.2, 3.1.3, 3.2.1–3.2.3, 4.1.7–4.1.9 and 4.2.2–4.2.5. The item's source stops at the reduced-fibre preparation, before the later Cohen–Gabber finite presentation. Its statement agrees with that preparation. No statement correction or dispute is needed. In particular it does not assert prime-to-ell degree, a coefficient DVR with the entire residue field of C, or the later etale finite presentation.

I clarified step 7: integral transitivity is applied to T_i inside D_i inside D_i[x], after showing the last extension is finite from a monic equation. This makes the statement of the cited transitivity node apply literally. I replaced the inherited generic tool-use explanations with the actual assertion each step needs, and added already logged second phrasings for the perfect-core node to its search record.

### Search evidence

Read the saved search outputs and searches.jsonl, including successful LeanFinder, LeanSearch, Loogle and grep results. For Epp, both the single-trait and finite-family phrasings return tilt, Witt-vector DVR, unramified-locus and good-reduction declarations, not normalized Epp base change. The grep matches of Epp in RingTheory are local variable ePp, as the recorded lines show. The Loogle pattern IsDiscreteValuationRing, IsReduced has no hits. For the perfect-core input, second phrasings about maximal perfect subfields and the Epp property return perfect closures, separability and algebraicity of perfect closures. I also opened Mathlib/FieldTheory/PurelyInseparable/PerfectClosure.lean: its relative perfect closure is the union of elements having some p-power in the base field; our core is the intersection of all p-power images. That file therefore does not assert our complete-local fraction-field lemma. PerfectField, IsAlgebraic has no Loogle hit. All recorded queries are preserved exactly from the actual search log, with no unavailable service reported as a negative result. These are two unsplit nodes and zero Mathlib leaves.

Whole-DAG concept/source searches found no existing Epp input. Repeated whole-blueprint searches Epp, perfect subfield, normalized base change and complete local fraction field returned no matching imported nodes. The ancestor command identifies lem-per-artin-gabber-affine-curve, agreeing with both new nodes' from.node and the retained via chain. Read the current ancestor split and the parent's step 6: this item prepares the special fibre for the mixed-characteristic branch of lem-per-cohen-gabber-finite-presentations. The unit and chapter records are unchanged. Generic commutative-algebra tools are declared in split_report.tool_uses for maintainer review, not installed as maintainer-owned tool_uses.

### Unfinished work

No unfinished part of this split. The two new supporting statements remain unsplit, as required; their proofs are future items. No Lean was written, and no compiler, Lake or build command was run.

## Not duplicates

lem-per-epp-perfect-core-complete-local vs lem-per-mixed-reduced-special-fibre-cover: the new node concerns characteristic-p fraction and residue fields of an arbitrary complete local domain, with a specified perfect subfield; it constructs neither a finite mixed-characteristic cover nor a reduced special fibre.

lem-per-epp-finite-family-traits vs lem-per-mixed-reduced-special-fibre-cover: the new node takes a finite family of DVRs and constructs one base-DVR extension; it makes no higher-dimensional local normalization, dimension or equidimensionality assertion. Steps 1–2 and 4–10 of the item supply those arguments.

lem-per-epp-perfect-core-complete-local vs lem-per-coefficient-field-generic-differential-basis: the existing node produces a coefficient section and differential basis in a reduced equidimensional ring, not algebraicity of the maximal perfect subfield of a fraction field. Both use Cohen structure, but their conclusions differ.

The new nodes have no Stacks tags in common with existing nodes: their sources are respectively ILO IV 3.2.3(i),(iv), and IV 3.1.2–3.1.3 with the simultaneous-base-change sentence of IV 4.2.3. No existing node states either conclusion. They are tools of different mathematical type from the item, not clauses renamed as lemmas. The other required algebra results were reused rather than recreated.

## Review by Q83

I read the node files, not just their dependency names. I checked the current item statement against ILO IV 4.2.3–4.2.5: A is complete Noetherian normal local and mixed characteristic; a component of the normalized finite base change is a finite domain over A; its coefficient trait has perfect residue field; the special fibre is reduced; catenarity supplies dimension d-1. The residue field finiteness follows from module finiteness, and the maps are injective and local as shown explicitly. The d>=2 assumption is retained, although the reduced-fibre preparation itself also works in dimension one.

For the first new node I read IV 3.2.3(i),(iv) and its Cohen-structure argument. The fixed perfect subfield version uses a coefficient field compatible with that subfield, not an arbitrary section silently treated as compatible. This is the version used in IV 4.2.3. For the second I read IV 3.1.2 and the noncomplete-upper-trait extension explicitly stated in 3.1.3, as well as the finite-family/stability sentence in 4.2.3. Excellence is imposed on the upper DVRs, which our application verifies; completeness is imposed on the base trait, not on the localizations A_{P_i}. In characteristic zero the tensor of the two fraction fields is reduced and finite dimensional, so it is a product of fields. The node explicitly states its assertion for each field factor, making the normalization in step 7 eligible. The residue field of the finite base DVR extension is finite over the perfect base residue field and is consequently perfect.

Step 1: lem-weil-pbc-cohen-rings-exist gives a Cohen ring for k_*; def-weil-pbc-cohen-ring gives its complete DVR structure and uniformizer p. The statement of lem-weil-pbc-cohen-ring-mod-pn-formally-smooth explicitly gives the square-zero lifting used here. Its exponent is n+1; p^{n+1} vanishes in A/m^{n+1}, and (m^n/m^{n+1})^2=0 for n>=1. def-weil-pbc-adically-complete-ring identifies A with the required inverse limit. The DVR unit-times-power statement gives injectivity into the characteristic-zero domain. The perfect-core field calculation and residue-locality assertion are explicit elementary arguments, not uncited structure theorems.

Step 2: finite-minimal-primes gives the finite list. For A/pA, its support is V(p): if a prime omits p the quotient localizes to zero, while otherwise p is in the maximal ideal of the local ring and the quotient is nonzero. Hence minimal-support-prime-associated applies to this finite cyclic module, and normal-domain-principal-quotient-associated-height gives height one for each P_i since p is nonzero. The localization-noetherian and localization-normal-domain statements give exactly the hypotheses of normal-dim1-dvr. Dimension one is the prime-chain description of height. Complete-local-excellence applies to A; finite-type-localization-excellent applies with A itself as its finite-type algebra. This verifies the excellence needed in the Epp node, without assuming a noncomplete trait is complete.

Step 3: complete-local-quotient applies to the proper prime P_i. The quotient is a characteristic-p domain, and its residue field is k. The coefficient map factors through W_0/p because p is zero there; a unital map from a field is injective. The new perfect-core node gives precisely the residue-field hypothesis for the new finite-family Epp node. The finite list is from step 2, its traits are excellent DVRs with local injective W_0 maps, and W_0 is complete with perfect residue field. Thus every Epp hypothesis has been checked.

Step 4: the integral-closure-finite-extension-normal statement includes normality, domain structure and fraction field L, not just integral closedness. Complete-local-nagata together with the definitions Nagata and Japanese gives finite normalization of A/(0)=A in the finite extension L/F. Finite-algebra-is-integral applied to W/W_0 gives W inside C. The choice of L is legitimate because tensoring a basis makes F tensor K a nonzero finite dimensional F-algebra, and a maximal quotient is a finite field extension. No assertion about locality is taken from the choice of field factor.

Step 5: finite-over-complete-local-product explicitly includes the domain consequence: C is Noetherian complete local with its unique prime above m. Finite-algebra-is-integral and integral-injective-dimension-equal then give dim C=d. The unit-times-uniformizer-power statement applies in W. Because W/W_0 is local and mixed characteristic, p has positive pi-valuation, which proves the W-to-C map local. Finite A-module generators reduce to spanning vectors of the residue extension; no finiteness of k over k_* is assumed.

Step 6: going-down-normal-integral states existence of a lower prime under a specified upper prime. Applying it successively to a chain of length two under P would give a length-two chain under height-one Q, impossible. Here A is normal and A inside C is an integral inclusion of domains. P contains the nonzero p, so height P is one, and a smaller prime containing p would give the forbidden two-step chain from zero. This verifies that the chosen Q lies over one of the actual Epp traits.

Step 7: integral-closure-commutes-localization states exactly the comparison with the integral closure of A_{P_i} in L. The image D_i of the tensor algebra is finite over T_i because generators of W over W_0 span its tensor algebra and image. Finite-algebra-is-integral and integral-transitive now compare the integral closures in both directions, with D_i[x] written out in the repaired sentence. The field F is also Frac(T_i); the factor L is therefore one of the field factors explicitly covered by finite-family-traits. That node's statement gives reducedness of C_i/pi, not merely of some unrelated normalization.

Step 8: the localization and quotient identification is written on fractions; reducedness is proved directly by multiplying a nilpotence equation by a denominator. This step is elementary and has no hidden cited theorem. It gives reducedness of C_Q/pi C_Q for every height-one Q containing pi.

Step 9: normal-domain-principal-quotient-associated-height applies to C and nonzero pi. Its statement controls all associated primes of M=C/pi C, not only minimal primes. Localization-at-prime-of-quotient identifies the localized quotient on the same fractions. Module-injects-localizations-associated-primes explicitly gives the needed injectivity for this Noetherian C-module. Every nilpotent has zero image at each of those primes by step 8, hence is zero. This is the associated-prime version of ILO IV 4.2.4; no unsupported assertion that normal principal quotients are reduced is used.

Step 10: complete-local-excellence applies anew to C. The definition of excellent ring includes universal catenarity and explicitly says saturated chains between fixed primes have equal finite length; take its finite-type algebra to be C. The two associated-prime nodes give height one for every minimal prime of pi C, just as in step 2. Concatenating (0)<Q with a saturated chain above Q proves dim C/Q=d-1 directly from this definition. There is no uncited dimension formula hiding behind an identification. These are exactly the dimensions of the minimal components of C/pi.

Small cases: for the perfect-core lemma R=k is the hypothesis itself, and R=k[[t]] has perfect core of its fraction field equal to k_perf, as in IV 3.2.3(iii); no assumption that k is perfect was inserted. A finite extension over a perfect k_0 is allowed, and transcendental imperfect k with k_perf=k_0 is also allowed. For finite-family-traits the empty family takes W=W_0, and the singleton T=W_0 already has reduced special fibre; a ramified singleton requires Epp and is not falsely treated as reduced without extension. In the item p and pi are nonzero nonunits, so neither the vertical-prime list nor the quotient is an accidental zero-ring case. With d=2 each component of the special fibre has dimension one. An imperfect or infinite residue extension k/k_* is allowed throughout, as required by ILO.

I checked delivery-errors B–E: both new nodes introduce their own objects, explain the perfect-core and local-map conventions, cite the definition nodes they actually use, and contain statement only, no proof or proof dependencies. Their TeX is written once in JSON. No Mathlib leaf is claimed from a merely related hit. No node is an elementary step or a renamed clause of the item. Every non-elementary fact used in the proof is a cited statement, and every quoted sentence was checked verbatim. All ten steps are below 2000 characters (the longest is 1076); none hides an additional long comparison. The local normalization comparison was clarified rather than moved wholesale into a new lemma. The preliminary server checks found no introduced cycle or missing node. The full delivery dry run is the final gate before push.

### Full dry-run repair

The first full dry run rejected the perfect-core node because all three definition citations shared one bracket. I separated them into individual bracketed node citations and updated the corresponding verbatim quotation. This is a citation-format repair only; no mathematical statement or hypothesis changed. The step-9 warning about ILO 4.2.4 refers to the item’s own source: step 9 writes its proof using the associated-prime statements, rather than using an uncited external lemma.
