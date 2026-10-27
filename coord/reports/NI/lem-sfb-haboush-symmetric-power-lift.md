# Stage-1 delivery: lem-sfb-haboush-symmetric-power-lift

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-haboush-symmetric-power-lift.json: statement unchanged, split into seven proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-torus-simply-connected-cover.json: statement, unsplit; no Mathlib match after two natural-language phrasings, Loogle, grep and LeanSearch.
- dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-endomorphism-detection.json: statement, unsplit; no Mathlib match after the same search types and two phrasings.
- citations.json: every proof citation, with the verbatim statement actually read.

## Attachments

None. The searches of lean/WeilConjectures/ by the item tag, Haboush, geometric reductivity, Steinberg and central isogeny found no declaration stating the item or the two new nodes. Abstract-group/Lie-algebra results are not rational algebraic-group theorems in arbitrary characteristic.

## Wanted literature

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Lemmas 9.7.2, 9.7.4 and Theorem 9.7.5, printed pp.49--50, and Lemma 9.2.5/Remark 9.2.7, pp.43--45, for the item and lem-sfb-steinberg-endomorphism-detection. The repository does not contain literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf. I read https://arxiv.org/html/1005.2398v3#S9.SS7 and the online PDF; nothing was downloaded into the repository. The item is marked proof_origin.by=agent because the field-only reductions, Laurent coefficient calculation and coefficient descent are written here.

## Corrections and scope

The item's statement and stmt_deps are unchanged. Its imported proof was empty. The proof now exposes the determinant construction, rather than introducing an equivalent polynomial-separation theorem as the only new dependency. The hard representation-theoretic input is an endomorphism-valued linear detection statement for simply connected semisimple groups; it does not state the item's invariant symmetric-power conclusion. Its two clauses are the two outputs used together in Alper's construction, before normalization and taking a determinant.

The inherited blueprint.from.node is null. Running tools/blueprint_refs.py ancestor on this item confirms that value. Following created.item reaches lem-sfb-admissible-direct-image, created for a Lean module, which points to the non-imported det-thm-sf-ctf-stability-direct-images. I retained the null ancestor, the exact existing via chain, and the supporting-proof place; the new nodes prepend the item to that chain. Searches of the whole imported blueprint for Haboush, central isogeny, diagonalizable and Steinberg found no counterpart (the sole Steinberg result is Lang--Steinberg for a semilinear Frobenius, a different theorem). The chapter/unit route and records were not changed.

## Source error

Source caution: Alper's displayed Lemma 9.7.2(2) needs the invariant vector to be nonzero modulo the maximal ideal: with v=0 its displayed nonzero conclusion is impossible. The following Theorem 9.7.5 applies it to a primitive invariant vector. The new field detection node explicitly assumes x nonzero. In the field version, extend the split group and the representation constantly to F[[t]], apply the primitive-vector form, take m sufficiently large and (in characteristic p) m=p^nu-1, use self-duality from 9.7.4, and reduce the map modulo t. The invariant tensor line of 9.7.2(1), in the residue-field form of Remark 9.7.3, becomes End(E)^S=F id. These are sources for the statement-only node, not an additional proof hidden in its statement. The whole node remains open for its future worker.

## Not duplicates

lem-sfb-reductive-torus-simply-connected-cover vs lem-sfb-pgl-reductive-structure: the latter asserts that PGL is reductive, whereas the new theorem supplies a product covering for an arbitrary reductive group over an algebraically closed field.

lem-sfb-reductive-torus-simply-connected-cover vs lem-sfb-haboush-symmetric-power-lift: the new node is a structural isogeny theorem with no representation or symmetric-power lifting conclusion.

lem-sfb-steinberg-endomorphism-detection vs lem-sfb-haboush-symmetric-power-lift: the new node produces a linear map to an endomorphism representation with scalar invariant endomorphisms, only for simply connected semisimple groups over algebraically closed fields. It gives neither a symmetric-power invariant nor an arbitrary-field lift. The item's proof must construct the determinant, handle the central torus, identify the correct dual polynomial space and descend the coefficients.

lem-sfb-steinberg-endomorphism-detection vs lem-sfb-pgl-geometric-reductivity: the existing node gives power lifting and finite generation for PGL algebras and already depends on the item. The new node is the independent representation-theoretic input for a simply connected semisimple group; no algebra invariant-ring finiteness or power lifting appears in it.

lem-sfb-steinberg-endomorphism-detection vs lem-sfb-comodule-finite-subrepresentation: the latter finds a finite-dimensional subrepresentation containing an element of a given comodule; it neither constructs a detecting map to End(E) nor proves that the invariant endomorphism space is a scalar line.

lem-sfb-steinberg-endomorphism-detection vs lem-sc-lang-steinberg: Lang--Steinberg here means surjectivity of F-1 for a p-linear endomorphism, with no reductive-group rational representation content.

## Review by NI

I read the full worker brief, stage-1 contract, the three blueprint levels in SETUP, GOAL, the chapter and unit records, and both copies of delivery-errors B--E. I read the item's actual statement and its parent's use: the parent needs the invariant q to map to exactly 1, in every characteristic over the original field. That is the conclusion proved here. I searched the complete DAG statements and whole imported blueprint before creating the two new nodes. I retained the item's existing five Mathlib search records and read their hits; their question and the item statement have not changed. Every new-node search in the delivered JSON was actually run by msearch.py for this item and its full response is retained in search-results.json and the command's searches.jsonl. All services answered; no unavailable response is treated as an absence result. The returned Schur lemmas, Lie algebra radical results, abstract centers and finite-group averages do not construct either of the two required algebraic-group inputs.

For the cover node I read Milne's local PDF: Proposition 21.60, including its almost-direct-product proof using the central torus radical and the derived semisimple group; Proposition 19.21(c); and Theorem 18.25/Remark 18.27 on the simply connected covering. These provide the factors and finite central kernel used here. Over the algebraically closed field all tori split. A quotient homomorphism in these structural results is faithfully flat; its coordinate pullback is injective. No SGA reference or source is used.

For the detection node I read Alper 9.7.2, Remark 9.7.3, 9.7.4 and the endomorphism step of 9.7.5 online. I checked that large p^nu-1 values may be chosen in positive characteristic and that characteristic zero has no prime-power restriction. The vector must be nonzero, as discussed above. The module E is nonzero because the detected endomorphism is nonzero. The statement uses the conjugation representation and coaction invariants, so it supplies precisely the two facts used in step 4. It is genuinely representation theory to be split next; no theorem is claimed finished.

Step 1 cites the entire statement of def-weil-algebraic-closure, which explicitly states existence of an algebraic closure. Surjectivity of lambda makes x nonzero; the contragredient formula proves its invariance. The geometric definition of reductive makes H_K reductive. The symmetric-power base change identification is written on actual monomials, hence uses no assertion about duals of symmetric powers or factorials.

Step 2 uses the new cover statement, read in full, for T, S, p and its injective coordinate pullback. Its field and reductivity hypotheses were established in step 1. Step 3 uses no unrecorded representation-theoretic theorem: the Laurent-basis coefficient equations prove the weight decomposition, its directness, and the commuting S-action preservation in a few lines. This is the coassociativity proof in Milne 12.12, read at printed pp.234--235. The projection fixes x because x has trivial torus character. Thus U is finite dimensional, rational, and has a nonzero invariant x, exactly the detection node's hypotheses.

Step 4 uses the detection statement's nonzero image and scalar invariant-endomorphism equality. Since E is nonzero, the scalar c is nonzero, so normalization by c inverse is legitimate. In particular the determinant degree n is strictly positive; a zero-dimensional E would give only degree zero and is explicitly excluded.

Step 5 cites the existing determinant definition for the actual signed-monomial element and the entire Cauchy--Binet statement for multiplicativity, using only its square case with its unique full-size subset. I read both node statements. Stacks algebra.tex line 282 and tags/tags identify the source as 0F0K, algebra-item-cauchy-binet. The calculation takes place in a polynomial coordinate ring tensored with K[S]; this proves the coaction identity even for universal points, rather than only invariance under K-points. det(I)=1 follows directly from the cited signed permutation formula. The conjugation inverse is an invertible matrix over this commutative algebra, and cancellation uses det(B)det(B inverse)=1, not a characteristic restriction. Cauchy--Binet is a general tool from another unit; it is declared in split_report.tool_uses, with the reason, rather than altering the top-level tool_uses field.

Step 6 cites no additional theorem: the two equivariance identities give product invariance, injection is checked coefficientwise, and the double-dual comparison is written on a basis and checked against the contragredient action. Evaluation at the fixed covector is precisely the map induced by lambda, as checked on each generator of the free commutative algebra. This avoids the false identification of Sym^n(V dual) with the dual of Sym^n(V) in small characteristic.

Step 7 is coefficient descent: choose a finite k-linearly independent coefficient set containing 1, then extract its coordinates in the invariance identity and the scalar image identity. Both equations are linear over k in the coefficients of the fixed degree. There is no averaging over a finite extension and no separability assumption, so imperfect and finite ground fields are included. The constructed coefficient q_0 has image exactly 1.

I checked small cases: a surjection rules out V=0; for H=1 the cover permits T=S=1 and detection can use E=K and a linear functional taking x to 1. For a torus the weight-zero projection alone retains x, including rank-zero torus. The structural cover allows a trivial semisimple factor, and finite central kernels may be nonreduced (no surjectivity on rational points is assumed). Positive characteristic, particularly n divisible by the characteristic, causes no division by n or n!. For x=0 the new detection conclusion would fail, so x nonzero is essential and present. All seven steps are shorter than 2000 characters, and all cited quotes in citations.json are literal node statement strings. The statement-only new nodes have no proof steps or proof dependencies and do not restate the item's conclusion.

## Unfinished work

No gap is left in the natural-language argument of the item beyond the two explicitly stated unsplit inputs. Those two nodes require their own future splits. No Lean file was written, and no compiler or Lake/build tool was run.

## Validation

The initial repair dry run exited successfully: `OK (not pushed) deliver/NI/lem-sfb-haboush-symmetric-power-lift at 63caee41cfe: preflight passed`. A final dry run follows the repair edits below, before pushing.


## Repair of the 2026-10-22 return

The return names delivery head `41e142d4da3` and says that the independent reader approved the mathematics, but landing could not promote the side completion into the live DAG. I continued the retained sandbox of that delivery, rather than treating the side completion as a live finished item. The current read clone has the item `unsplit`, with empty proof and no reviewed record; neither new input exists there. The item statement, statement dependencies, source, blueprint ancestry and inherited Mathlib records agree with the retained version. The delivery command constructs the repaired commit on the freshly fetched `origin/sheaf-dag` and preserves the current maintainer-owned fields. This is the rebase requested by L; promotion remains L's landing operation, not a worker edit to review/queue records.

I re-read every existing proof dependency, whether changed or not: `def-weil-algebraic-closure` explicitly includes existence; `def-weil-pbc-matrix-determinant` supplies the signed permutation formula; and `lem-weil-pbc-cauchy-binet` supplies the formula whose square case is multiplicativity. Their current statements still contain every verbatim quote in citations.json. I also re-read both retained new statements and checked steps 2 and 4 against their actual field, reductivity, nonzero-vector and rational-coaction hypotheses. No dependency replacement or statement change is required by current main. The two new nodes remain statement-only, with their recorded searches and sources retained. There is no released stage-1 repair note for the item.

I re-opened Alper's online §9.7 (9.7.2--9.7.5), Remark 9.2.7 and the field formulation 9.2.8, and Milne's local PDF at 12.12, 18.25/18.27, 19.21(c) and 21.60. These still support the cover/detection/determinant route read by the first reviewer. The Alper PDF is still WANTED. The actual JSON uses correctly escaped TeX; its decoded proof has single command backslashes, so no TeX rewrite was needed.

I strengthened step 6 during this repair: instead of only saying that the commuting identities give product invariance, it now writes the action of an arbitrary pair `(t,s)` and then specializes to the universal pair over the coordinate algebra. This makes explicit why the claim is a coaction identity and handles nonreduced central kernels without relying on rational points. The remainder of the retained seven-step argument and both unsplit inputs are preserved. All steps remain below 2000 characters. I checked the trivial group, trivial torus factor, trivial semisimple factor, nonzero fixed vector, and arbitrary positive characteristic again; the coefficient descent still extracts q_0 with image exactly 1 over the original field.

This section is NI's return-specific review in addition to `## Review by NI` above. The repair addresses the sole return point by preparing the live-base delivery and revalidating all citations, with the explicit step-6 adjustment. No repository, launcher, Lean source or build was changed or run by this worker.


## Resumption check after provider interruption

No delivery process for this item remained active. The retained dry-run receipt was preserved; the first resumed dry run exited 0 with `OK (not pushed)` at `824262e84ce`. I compared the retained item against the current read clone: only proof, proof dependencies, proof origin, status and split report differ. Its statement, statement dependencies, source and blueprint ancestry still agree. The current item is unsplit and has no reviewed record, and neither new input exists in the current read clone. There is no repair note. Thus the side completion has not been mistaken for a live completion.

I opened all five cited statements again and checked every quote literally, including both retained new inputs. The three existing inputs still supply exactly algebraic-closure existence, the signed determinant formula, and Cauchy--Binet. Step 2 has the algebraically closed field required by the cover theorem; step 4 has the nonzero fixed vector and finite-dimensional rational module required by detection. Steps 3, 5, 6 and 7 retain their explicit Laurent-coefficient, universal conjugation, product-coaction, and coefficient-descent arguments. The universal-pair repair in step 6 remains present. Every step is below 2000 characters. The new inputs remain unsplit statement-only nodes. I rechecked their trivial-group cases and the absence of characteristic-dependent division.

I reopened [Alper, section 9.7](https://arxiv.org/html/1005.2398v3#S9.SS7), particularly 9.7.2--9.7.5, and Milne's local Proposition 21.60 with its proof. The latter is on printed p.442 (PDF p.454), so I corrected the cover node's source locator from p.441 to p.442. The proposition number and mathematical input are unchanged. The Lean source search again found no Haboush, symmetric-power-lift, central-isogeny or detection declaration. The retained Mathlib searches and their results were reused; none was invented or rerun. The fresh whole-DAG keyword search and blueprint Haboush search found no duplicate of either input. The ancestor command again returns null, agreeing with the retained ancestry explanation. A final dry run after this locator/report correction precedes delivery.


## Repair revalidation on 2026-10-23

The current return entry in coord/returns/NI.md names head `5097f801eaa`, with the same landing/promotion refusal as the earlier return recorded above. I compared the retained sandbox with the current read-clone DAG: the item remains unsplit, both new inputs remain absent, and only the split-owned proof, status and split-report fields differ. Its statement, statement dependencies, source and blueprint ancestry agree. There is no item repair note. No live completion has been used to bypass the requested repair.

The interrupted first dry run no longer had a running process or readable session; its durable receipt records head `f26aea110b5`. A fresh dry run was therefore run once and polled to exit 0: `OK (not pushed)` at `25739f05033`, with server preflight passed. These receipts are validation records, not evidence of a push. The final dry run below covers this repair's edits before delivery.

I re-read all five proof-cited statements and checked each literal quote in citations.json. Algebraic-closure existence remains explicit in def-weil-algebraic-closure. The retained covering statement gives the faithfully flat map and coordinate injection over the algebraically closed field established in step 1; its finite central kernel need not be reduced. The retained detection statement applies to step 3's finite-dimensional rational S-module and nonzero fixed x, and gives a nonzero E, nonzero image and scalar invariant endomorphisms. The determinant definition and Cauchy--Binet still give exactly the signed formula and its multiplicativity specialization in step 5. None of these statements requires a changed hypothesis or citation. I checked their definition dependencies as well.

I re-opened Milne's local Proposition 21.60 (printed p.442), Theorem 18.25/Remark 18.27 (p.393), and Theorem 12.12 with its coassociativity proof (pp.234--235), and Alper's online section 9.7. The local Alper PDF is still absent and the existing WANTED record is retained. New-node sources, search records and saved responses remain intact. The saved search hits concern abstract groups, Lie algebras or general Schur lemmas; none constructs the covering or detects the fixed vector for rational algebraic-group representations in arbitrary characteristic. Fresh project-source and whole-DAG/blueprint searches found no finished attachment or replacement input.

As an additional concrete clarification in this resumption, step 7 now explicitly uses 1 nonzero to extend the singleton {1} to the coefficient basis. This justifies extracting the coefficient whose image is exactly 1, rather than only nonzero. I retained the earlier universal product-coaction repair in step 6. I checked all seven steps for hidden inputs: torus projection is the written Laurent-coefficient computation, determinant invariance is the universal matrix identity over a commutative coordinate ring, and scalar descent is the written basis-coordinate argument. Each step remains under 2000 characters. The trivial group, rank-zero torus, trivial semisimple factor and positive characteristic still satisfy the argument without division by degree or factorials. Both new nodes remain statement-only and strictly narrower inputs. This revalidation supplements my signed Review by NI above and addresses the return against the current DAG.
