# Stage-1 delivery: lem-per-gabber-regular-pair-purity

Group Q53; 2026-10-19. This resumes the earlier sandbox. Its six child statements, searches, citations, and proof have been retained. The initial required dry run exited with the missing-report diagnostic; the subsequent server-only check_dag and review_split both passed before the citation repairs below. No Lean was written and no compiler, Lake, local DAG checker, or git command was run by the worker.

## Files written

All node files are under dag/nodes/sec-deligne-laumon-a1/.

- lem-per-gabber-regular-pair-purity.json: statement; split into six proof steps; no exact Mathlib match.
- lem-per-gysin-coefficient-cone-triangles.json: new statement-only input; no Mathlib match. Compatible cones of the actual etale supported classes, not just existence of a triangle from an arbitrary short exact sequence.
- lem-per-punctual-purity-two-of-three.json: new statement-only input; no Mathlib match. Relates pair purity with punctual purity of the ambient and closed schemes.
- lem-per-punctual-purity-trait-test.json: new statement-only input; no Mathlib match. Reduces universal punctual purity to the mixed-characteristic complete strictly henselian trait test family.
- lem-per-log-smooth-trait-punctual-purity.json: new statement-only input; no Mathlib match. Punctual purity for regular fs log-smooth schemes over a trait.
- lem-per-trait-prime-to-ell-log-alteration.json: new statement-only geometric input; no Mathlib match. Projective generically etale prime-to-ell alteration to a regular log-smooth scheme over a finite trait extension.
- lem-per-punctual-purity-proper-degree-descent.json: new statement-only input; no Mathlib match. Proper invertible-degree descent of punctual purity over the test traits.
- citations.json: one verbatim statement quotation for every node used by every proof step.
- report.md: this report. The pre-existing search plan, searches.jsonl, output files, extracted literature and writing scripts remain in the sandbox as working evidence; they are not changes to project sources.

Six new nodes, zero new Mathlib leaves. Existing Mathlib leaves are reused in Step 1.

## Attachments

None for the item or its new nodes. I searched the project source for the item's exact blueprint tag and for Gabber, absolute purity, punctual purity, and log smoothness. The relevant file WeilConjectures/EtaleCohomology/Purity/Smooth/RegularImmersion.lean has isIso_fundamentalClassMap and the associated class construction, but these are sorry declarations and impose smoothness over a perfect field. They cannot attach the present Noetherian regular-pair statement. The weight-purity declarations concern Frobenius weights, not cohomological absolute purity.

The already existing lem-pc-projective-proper is used by its statement; its recorded closed project Lean is not a new attachment claim.

## WANTED

None. The available ILO volume explicitly states the reductions and component results used here. The original Fujiwara article is not independently claimed to have been read: the reduction is read in ILO XVI 3.7 and the completion and equal-characteristic assertions in XVI 3.2.4--3.2.5.

## Problems found and changes made

The repository item's statement agrees with ILO XVI Theorem 3.1.1 and remains unchanged. The saved copy differs from the current repository only by its proof, proof metadata, searches, status and split_report. The original item had no proof. It is not legitimate to apply the existing smooth-over-a-field purity declaration or an excellent-scheme alteration assertion directly to its unrestricted X. The split instead uses ILO's trait test before alteration.

On resumption the report was missing. I read delivery-errors B--E whole and repaired three missing generic tools in the saved proof: Step 1 now uses the existing Hom-exactness and cone-zero nodes instead of leaving exactness of triangle cohomology implicit; Step 4 cites projective implies proper; Step 6 cites the signed finite Tate-line theorem, since the positive-twist definition by itself does not assert invertibility. No new helper node was introduced for any of those tools. Coefficient reduction is performed on compatible cones of the actual supported class, not on an unproved exceptional coefficient-base-change comparison.

The item is not a key statement node of sk-p-dl-a1-perverse, so no realized fields of that unit are changed. The chapter and unit records were read. The ancestor lem-per-artin-gabber-affine-curve is the imported route place for this local regular duality input. The main-20261015 blueprint search found no additional node stating the new assertions. No prohibited SGA source is used as a delivery source: the proof follows ILO XVI. Its internal bibliography is not substituted for any step's node citation.

## Not duplicates

The whole DAG was searched by the words punctual purity, log smooth, Gysin, coefficient cone, proper degree descent and prime-to-ell alteration, and by the relevant ILO XVI places. Whole-blueprint searches included punctual purity, log smooth, Gysin, alteration, regular pair, and projective proper. The Frobenius weight-purity hits do not state any of the six assertions. In particular:

lem-per-gysin-coefficient-cone-triangles vs lem-per-regular-immersion-class-calculus: the existing node supplies classes and coefficient compatibility, but not compatible cone representatives or coefficient-exact distinguished triangles.
lem-per-gysin-coefficient-cone-triangles vs lem-per-absolute-gysin-purity: the existing node is the parent Gysin theorem for finite-type affine regular schemes; it does not state the coefficient-exact cone construction and depends on the present item.
lem-per-punctual-purity-two-of-three vs lem-per-gabber-regular-pair-purity: the new node is the conditional two-of-three criterion, not the assertion that all regular pairs are pure. Neither punctual purity assumption is proved in that criterion.
lem-per-punctual-purity-trait-test vs lem-per-gabber-regular-pair-purity: the new node is the reduction implication from a particular mixed-characteristic test family to all regular schemes. The geometric and cohomological arguments establishing the test-family premise remain in Steps 3--4.
lem-per-log-smooth-trait-punctual-purity vs lem-per-gabber-regular-pair-purity: this is the smaller log-smooth-over-a-trait case, not purity of arbitrary pairs. The trait reduction and alteration/descent are still required.
lem-per-trait-prime-to-ell-log-alteration vs lem-per-prime-to-ell-uniformization-standard-form: the existing quasi-excellent-scheme assertion supplies a modification and an etale/finite-flat family; it does not supply a single projective generically etale map from a regular log-smooth scheme over a trait extension.
lem-per-trait-prime-to-ell-log-alteration vs lem-per-gabber-prime-to-ell-regular-cover: the regular-cover assertion supplies a covering family in the alteration topology, not the stronger trait-relative log-smooth geometric structure required here.
lem-per-trait-prime-to-ell-log-alteration vs lem-per-gabber-regular-pair-purity: the new statement is entirely geometric and has no purity conclusion.
lem-per-punctual-purity-proper-degree-descent vs lem-per-gabber-regular-pair-purity: the new statement transfers punctual purity under a proper map of invertible generic degree; it supplies neither a pure cover nor purity of a general pair.
lem-per-log-smooth-trait-punctual-purity vs thm-pur-affine-line-purity: the blueprint theorem is smooth affine-line purity in its fixed finite-field coefficient setting; it is not punctual purity for regular log-smooth schemes over mixed-characteristic traits.

The six new statements are genuine component results of XVI 3.2, 3.3, 3.5, 3.6 and 3.7, not elementary intermediate calculations. The cone induction, inverse-line calculation and final degree calculation stay in the item's proof.

## Mathlib search review

I retained the exact tool/query/results entries and inspected the saved searches.jsonl and the result files. Each new node has two distinct LeanFinder formulations, Loogle, grep and LeanSearch results. The item retains its prior searches and the saved later search set. No query was fabricated or silently replaced, and no service failure is used as evidence of absence. The available searches returned no matching absolute etale purity or logarithmic theorem. In particular, DerivedCategory.triangleOfSES and HomologySequence.exact_* supply general derived-category exactness, not compatible representatives for the etale Gysin coefficient maps, so the coefficient-cone assertion is not a one-line specialization. The Loogle purity hits are Lean compiler LCNF.Purity; the Gysin grep hits are substrings of finestTopologySingle; neither is an etale purity theorem. The log-smooth searches return ordinary scheme smoothness, which is a different notion. These genuine returned results remain verbatim in the node records.

## Review by Q53

I read the item's ILO XVI Theorem 3.1.1 at printed p.242: its Gysin arrow is the supported class and its conclusion has the positive (c)[2c] on exceptional pullback. It does not impose excellence or a field base. I read the definition of regular-pair and punctual purity at pp.243--244, the two-of-three proof in Proposition 3.2.3, completion invariance 3.2.4 and the prime-field case 3.2.5. I read the compatible Godement cocycles and cone triangles in Proposition 3.3.2 at p.245, the full proper-degree descent diagram and degree computation of 3.5.7--3.5.10 at pp.249--250, the fs log-smooth purity theorem 3.6.2 and chart criterion 3.6.3 at p.252, and the final proof 3.7 at pp.254--255. These are the sources of the six new nodes, respectively: 3.3.2; 3.2.3; 3.7 with 3.2.4--3.2.5; 3.6.2; the geometric construction in 3.7; and 3.5.7. The new nodes remain statement-only. I did not insert proofs into their statements.

For Step 1 I opened the coefficient-cone statement: it gives the exact triangle for every a,b>=1 in the common larger coefficient category and explicitly calls these cones of the actual eta_r. The existing lem-weil-pbc-hom-into-triangle-exact supplies precisely the factorization of an identity with zero composite used in the induction. The existing lem-kun-distinguished-cone-zero supplies precisely the criterion turning cone vanishing into invertibility of eta_r. This repair makes the induction start at r=1 and advance by a=r-1,b=1, with no derived coefficient-exchange assumption.

For Step 2 the trait-test statement has exactly the quantified premise established by Steps 3--4: integral regular, flat, finite type and quasi-projective over the complete strictly henselian mixed-characteristic trait, with ell a unit. The completeness restriction is obtained by first using the local completion reduction 3.2.4 in the general punctual test and then the finite-type trait reduction cited in 3.7; it is not an assertion that a nonexcellent ring has regular completion morphism. Equal characteristic is included through 3.2.5. The implication's conclusion quantifies all regular Noetherian schemes, so no excellence is silently added to the original pair.

For Step 3 I opened both the alteration and log-smooth-purity statements. The former gives integral regular Y, the finite extension T/S, its log-smooth fs structure over T, projective f, its generic etale degree prime to ell, and quasi-projectivity and finite type over S. Thus the second statement applies over T; ell remains a unit by pullback from S. In ILO 3.7, an ell-Sylow H is used, the tame equivariant modification and quotient are taken, and log resolution gives the regular source. The generic degree is the index of H and hence prime to ell. This geometric construction contains no appeal to purity of the target. Normalizing the constants in the preliminary trait extension does not replace the target by an unrelated X: the morphism is still to the original X, as in the source's final diagram.

For Step 4 I opened the proper-degree descent statement and checked all of its assumptions against the alteration statement. Quasi-projectivity supplies the restricted ample setting of ILO 3.5.7. The new proof now cites the existing lem-pc-projective-proper for its exact first sentence, so properness is not inferred from the definition alone. No flatness of f is assumed. The degree d>0 has ell not dividing it, hence is invertible in F_ell. These are exactly the conditions of the descent node. The trait-test node is cited again to discharge the quantified premise, rather than treating the special test V as the original X.

For Step 5 I opened the two-of-three statement and the existing lem-per-regular-immersion-class-calculus. Both X and Z in the item are regular Noetherian with ell invertible, so Step 4 gives precisely conditions (c) and (b). The two-of-three criterion therefore yields condition (a) for the same supported class, whose Kummer sign and composition convention are fixed by class calculus. The coefficient induction from Step 1 then supplies the original exponent n; the criterion is not being used as a proof of universal punctual purity.

For Step 6 I opened class calculus, the ordinary etale derived-category definition and lem-asd-etale-finite-twist-pullback. The last gives signed, locally free rank-one finite Tate sheaves for any scheme where ell^n is invertible, not only schemes separated and finite dimensional or defined over a field. Evaluation is locally the ordinary rank-one evaluation, hence the inverse-line calculation is valid. The cochain degree convention puts the unique sheaf in degree +2c, not -2c. Class calculus explicitly gives open restriction and the codimension-zero identity normalization. The step's remaining calculations are elementary from these statements, and it is marked accordingly.

I tested the edge cases: identity and open-and-closed immersions at c=0 give eta=1; empty Z is vacuous; n=1 is the induction base; a=b=1 gives the first cone triangle; the closed point of a trait has c=1 and predicts H^2 with twist (-1); different locally constant codimensions are handled by open restriction. Log smoothness is not confused with ordinary smoothness, and the generic degree is required nonzero and prime to ell. All non-elementary steps are below 2000 characters, so no long step is hiding another lemma. Every step's uses equals its cited-node list and their union is proof_deps. citations.json quotes the statements actually supplying those claims, not their proofs.

The two off-unit non-Mathlib tools (projective properness and signed Tate-line evaluation) are explicitly declared in split_report.tool_uses. They are general tools supporting the ILO route; they do not replace a step of the perverse unit. The other two added tools are existing Mathlib leaves. No dependency is a new duplicate or a definition cited as if it proved a theorem.

## Unfinished

Nothing required for this one-level split. The six statement-only component nodes are intentionally left unsplit for later workers, as required. Delivery validation is recorded by the deliver.py result.
