# Stage-1 worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-p-independent-root-quotient-field.json: item, split in four steps; its statement is unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-p-independent-higher-power-monomials.json: one new statement-only input; unsplit, no Mathlib match.
- citations.json: six step/citation entries, each quoting the cited statement verbatim.
- searches.jsonl: actual msearch.py results, preserved in their original form.

One new node; zero new Mathlib leaves. The item now names the existing quotient-algebra and basis definitions among its statement dependencies. No repository, launcher or Lean file was written, and no compiler was run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for p-independence, p-bases, root quotients and pthRootAlgebra. Algebra.pthRootAlgebra_isField_finite_pow in RingTheory/PthRootFieldQuotient.lean:44 has the first-height field and scalar-power assertions under independent differentials. It does not state all heights or the specified basis, so it is not an attachment. Existing p-basis declarations likewise do not state the item or the new higher-height independence statement.

## WANTED

None. The relevant Stacks source files are present locally.

## Source and route

Read more-algebra.tex, Tag 09II, proposition-epp-essentially-finite-type, especially the paragraph at lines 35980–35993 constructing the root tower from a residue p-base. This paragraph asserts the finite stages are weakly unramified DVRs; the present item supplies precisely the finite closed-fibre field calculation behind that assertion. Read Tag 07P1, definition-p-basis, and Tag 07P2, lemma-p-basis, at lines 11345–11415 for the exact bounded-monomial meaning of p-independence. The higher-height statement is an agent-written algebraic refinement, not a claim that Stacks states it separately. The item's proof_origin is accordingly agent.

Read SETUP.md's chapter/unit/node restrictions, the chapter record, the unit record, and the latest blueprint's sk-thm-sf-ctf-stability/_section.md and both the stability and direct-image proof files. The current direct-image proof (3) proceeds via proper/open preservation and does not state this algebra lemma. Retained the item's honest historical provenance, with blueprint.from.node = null as printed by blueprint_refs.py ancestor; filled the new node's place by the specific finite-stage role and prepended the item to its via chain. No unit or chapter statement or route was edited.

## Searches and reuse

Searched the whole DAG for 07P1, 09II, 07DZ, p-independent, p-basis, root quotient, reduced monomial, power subfield and the proposed helper id; searched the latest blueprint text and ran blueprint_refs.py search for p-independent, p-basis, monomial, root, bounded monomials, higher power, power subfield and Frobenius endomorphism. The imported p-basis extension node is reused as background only; it does not state higher-height independence. The false-positive Nagata overlap-independent hits were read as unrelated.

The existing lem-sfb-simultaneous-root-algebra-api states the actual quotient's basis for every positive exponent, not just characteristic-p exponents. Its empty-tuple and quotient-map clauses are also enough here. Reused it in steps 1 and 2. Reused def-weil-ring-frobenius, whose statement includes the ring-endomorphism theorem for every iterate, so no separate Frobenius leaf was created. Both are present in the DAG; the former is in this item's own unit, and the latter is a Mathlib definition leaf. No off-unit non-leaf tool permission is needed.

For the new node, ran msearch.py LeanFinder twice with different higher-power subfield phrasings, LeanSearch, two Loogle patterns, and three source grep patterns. Read all returned hits. In particular, read Mathlib/FieldTheory/PurelyInseparable/PerfectClosure.lean:346–378: LinearIndependent.map_pow_expChar_pow_of_isSeparable and Module.Basis.mapPowExpCharPowOfIsSeparable assume a separable field extension and retain the scalar field. Here k/k^p is generally inseparable and the conclusion changes the scalar subfield, so these are not matches. The power-basis and algebraic-independence hits do not express the bounded p-independent claim either. Each query and actual result is recorded on the node and in searches.jsonl. All services answered; none was recorded as unavailable or as an unrun search.

For the item, ran its own quotient-field LeanFinder queries with two phrasings, LeanSearch, Loogle MvPolynomial, IsField, and RingTheory source grep. The hits give components (monic univariate power bases, Frobenius, perfect closure and facts about an already-given field extension), not the whole item. Kept the original item's search records and appended the searches actually run here. No unrun search was invented.

## Argument for the new input, for its later worker

The new node deliberately has only its statement, with empty proof and proof_deps. Its proof can proceed by induction on n. The n=0 family is the singleton 1 over k. In a relation at height n+1, write every exponent uniquely E=D+pF with 0<=D_i<p and 0<=F_i<p^n, and choose a_E in k with c_E=a_E^(p^(n+1)). The relation becomes

    sum_D b^D (sum_F a_(D+pF)^(p^n) b^F)^p = 0.

Every parenthesized p-th power is in k^p. The original p-independence makes each such p-th power zero. Frobenius is injective on a field: x^p=0 with x nonzero contradicts multiplication by (x inverse)^p. Thus each inner sum is zero. The induction hypothesis at height n gives a_(D+pF)^(p^n)=0 for every D,F, hence a_(D+pF)=0 and finally c_E=0. Only finite sums occur. This is a genuine induction on scalar subfields and multi-index digits; it has its own field-only statement and does not assert any quotient is a field, has a basis, or has powers in the base. The item still performs the quotient calculation and constructs inverses itself.

## What was wrong or corrected

No STATEMENT-DISPUTED issue was found; the item is true exactly as written, including n>=1, r=0, arbitrary imperfection and no finiteness hypothesis on k/k^p. The imported item had no proof. Supplied the proof and its dependencies. No target, imported blueprint text, source or maintainer field was changed. Added the missing explicit quotient and basis notion dependencies. Retained the previous search record and provenance rather than overwriting them.

## Not duplicates

- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-p-independent-root-quotient-field: the new input is independence of b-monomials inside k over its power-image subfields; the item concerns a different algebra, the root quotient, its basis and its field structure. No clause of the item states the new input.
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-epp-essentially-finite-type-traits: the existing node constructs ramification-eliminating extensions of fraction fields of traits, not linear independence inside a characteristic-p field.
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-dvr-normalized-finite-stage-descent: the existing node descends local properties of normalized DVR extensions from an algebraic extension to a finite stage; it gives no higher-height monomial independence.
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-dvr-perfect-residue-algebraic-tower: the existing node constructs an integral-closure DVR tower with perfect residue field; the new node is an input in a field and constructs no tower or valuation ring.
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-epp-weak-perfect-residue: the existing node is weak Epp for a map of DVRs with perfect residue field, not a field-only monomial statement for possibly imperfect k.
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-finite-free-field-fibre-dvr: the existing node assumes a field closed fibre to deduce the DVR property of a finite free algebra; it does not prove any independence in the coefficient field.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-independent-extends-to-p-basis: extension to a p-basis gives independence and spanning only over kK^p, with exponents below p; the new statement changes the scalar subfield and the exponent bound at every height, without extending the tuple.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-independent-insert-outside-span: insertion adds one element at the same height p; the new node retains the tuple and proves all Frobenius heights.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-basis-exists: existence gives a full p-basis over k^p, not higher-height independence for the prescribed possibly nonspanning tuple.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-basis-differentials-basis: the existing node gives a basis of a differential module from a full p-basis; the new node concerns only scalars and bounded products in k and uses no differential module.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-independent-maximal-superset: the existing node produces a maximal p-independent superset at height one, not independence at the higher power-image subfields.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-independent-differentials-independent: the existing node concludes independence of differentials over K, not bounded monomials over k^(p^n).
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-frobenius-image-field-tower-degree: the existing node assumes finite [K:K^p] and an entire basis and gives bases of successive power images plus degrees; our prescribed tuple need not span and k/k^p need not be finite.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-p-basis-complement-monomial-basis: the existing node starts from a whole p-basis and gives exponents below p over a complement-generated subfield; it does not change to k^(p^n).
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-pth-roots-extension-degree: the existing node gives degree of a root extension at height one under independent differentials; the new node is a scalar relation inside k at every height, without adjoining roots.

- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-smooth-curve-function-field-p-basis: the existing node constructs a single height-one p-basis for a smooth curve function field over an algebraically closed field; the new node treats any prescribed independent tuple in any characteristic-p field at every height.
- lem-sfb-p-independent-higher-power-monomials vs lem-per-cofinite-subfields-finite-extension-differential-rank: the existing node compares differential ranks in a finite extension over a filtered family of cofinite subfields; it asserts no bounded monomial independence.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-differential-zero-iff-pth-power: the existing node characterizes vanishing differentials over a perfect base; the new node assumes a bounded monomial relation hypothesis and concerns all power-image subfields.
- lem-sfb-p-independent-higher-power-monomials vs lem-weil-pbc-derivation-nonzero-on-non-pth-power: the existing node constructs a derivation on a finite-type domain over a complete local ring; the new node has only field and independence hypotheses and no derivation conclusion.
- lem-sfb-p-independent-higher-power-monomials vs lem-sfb-raynaud-faltings-normalized-reduction: the existing node constructs a finite extension and normalization with geometrically reduced fibres for a flat algebra over a complete DVR; it gives no higher-height scalar independence statement.

## Review by Q60

I read 09II's p-base preparation, 07P1's exact monomial definition, 07P2's surrounding argument, and varieties.tex immediately after 03SM (definition-absolute-frobenius, lines 7014–7029). The new higher-height independence input is the explicit digit induction above, extracted from the algebra needed by 09II, not attributed as a separate verbatim Stacks lemma. Its hypotheses introduce all objects: prime p, field k of characteristic p, a finite tuple including the empty tuple, and exactly the assumed monomial independence. Its statement includes the zero-height and empty-tuple conventions and no proof text. Source tags and labels were verified in tags/tags. The Mathlib candidates were read in their files, not accepted on search ranking.

For step 1 I opened lem-sfb-simultaneous-root-algebra-api and checked its statement supplies the basis for any n>0 over any commutative ring, and identifies the empty tuple quotient with R. Substitute exponent q=p^n, positive because p is prime. The basis contains 1, so uniqueness of coefficients proves injectivity and nontriviality directly; no domain or field property of the quotient is presupposed. I also read def-weil-pbc-free-module for the unique-expansion meaning used here.

For step 2 I opened def-weil-ring-frobenius and checked that its statement really includes the iterated ring endomorphism, not only a name for Frobenius. It requires p times 1 to be zero, which follows by applying the coefficient map to the equality in k. The quotient construction in def-weil-pbc-algebra-hom-quotient provides the coefficient homomorphism; each relation t_i^q=b_i is the defining relation of the actual quotient. Distributing the ring homomorphism over the finite basis expansion gives the displayed scalar formula. The cited root-algebra node really states a basis and the actual quotient, so no facts hidden in its proof are used. citations.json copies both whole statements for this step.

For step 3 I checked that the new input's hypothesis is exactly the item's assumption, with the same ordered tuple and characteristic. Its exponent range is E_i<q and its scalar subfield contains each a_E^q, exactly the coefficients in step 2. A nonzero z has a nonzero coefficient by the step-1 basis; the nonzero-power argument uses an inverse in k only, not in the as-yet-unproved field C_n. This avoids assuming the conclusion. def-weil-field states that inverse property. The full new statement and field definition are quoted for this step.

For step 4 I checked the only exponent subtraction: q>=1, so z*z^(q-1)=z^q. The inverse c^(-1) exists in k since step 3 proved c!=0. The constructed element is in the actual quotient; multiplying gives 1 on both sides by commutativity. The cited field definition says precisely that a nontrivial commutative ring with inverses for every nonzero element is a field. This final calculation is elementary, and no finite-dimensional-domain-is-field theorem is silently used.

Small cases checked: r=0 gives the singleton basis 1 and C_n=k; n=1 is the original hypothesis; n=0 in the new input gives 1 over k; perfect k permits only the empty p-independent tuple; k=F_p(s,t) with tuple s,t gives the expected p^(2n) monomials; a proper subtuple such as s in F_p(s,t,...) does not require any spanning or finite imperfection degree. A repeated tuple element, b_i=0, or b_i=a^p violates the hypothesis, as shown by its immediate bounded-monomial relation, so the nonreduced examples k[T]/((T-a)^p) are excluded. The new node's induction works at p=2, at n=0, and for r=0.

Checked delivery-errors B–E against the files: one complete statement-only new node, explicit notions and actual tags, TeX with single logical backslashes, genuine searches; every citation's statement supplies the claimed clause (six verbatim quotes); no invented definition theorem or off-unit non-leaf tool; the new input is not a quotient clause; no circular use of the item's conclusion; and no omitted scalar-transport or denominator argument. All four item steps are below 2000 characters. The split has no unresolved mathematical correction and no SGA citation.

## What remains

The new independent field-theory input remains an unsplit stage-1 node as required by a one-level delivery. There is no other unfinished part of this item's split. Server dry run and delivery are the final validation steps.

## Dry-run tool failure

The single required deliver.py --no-push invocation exited with code 1. It waited for server preflight admission, was admitted in slot 3 after 3412 seconds, and then srvpreflight.py raised subprocess.TimeoutExpired: its SSH invocation of tools/preflight_delivery.py timed out after 720 seconds. The delivery tool attempted its own automatic nocheckout.py fallback; that also raised subprocess.TimeoutExpired after 600 seconds. No check diagnostics or OK result were produced. The attempted delivery commit was 38473c76dce3aa1b371d78b94f20799dcf4c00ea against base 1a2e834161648052a8fd931e192b1fe3fe019dd8. This was a dry run only; no push was attempted. The completed sandbox split, report, citations and search log are retained for retry. No launcher script was edited and no check command was run manually on this machine.

## Resumed validation, 2026-10-24

Retained both node files, all previous mathematical arguments, citations, search records and the timeout history above. The required first retry of deliver.py --no-push completed successfully: server preflight admitted slot 9 immediately and printed `OK (not pushed)` at 08a8a21dcc8. The earlier infrastructure timeout did not recur.

Compared the sandbox item to the current live node: its statement and provenance are identical; the live node is still unsplit and unreviewed, and the new helper id remains absent. No stage-1 repair note for this item exists. Re-read the current latest blueprint unit and direct-image proof (snapshot main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8); the historical-support explanation is still accurate. Re-read the relevant Stacks paragraphs and current Mathlib separable-Frobenius candidates. The search questions and statements have not changed, so the recorded searches are reused rather than repeated.

Reopened every proof citation's current statement, checked all six citations.json entries verbatim, and verified each step's uses has exactly its citation entries. The root-algebra API still states the required actual quotient basis; Frobenius explicitly includes every iterate; the new input supplies exactly the scalar independence required in step 3; the field definition supplies the inverse criterion. The displayed scalar formula and inverse construction remain valid for the empty tuple and for arbitrary imperfection degree. Steps have respectively 429, 429, 500 and 254 characters, so none hides a long argument. Repeated the project-source attachment search: no exact item declaration was found; the related pthRootAlgebra theorem is at current line 44 and still covers only height one and no specified basis. Expanded Not duplicates with the additional current same-tag neighbours after reading their statements. No mathematical node changes were necessary. The updated report is validated again before pushing.
