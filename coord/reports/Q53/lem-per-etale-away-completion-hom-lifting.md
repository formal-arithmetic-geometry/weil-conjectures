## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-away-completion-hom-lifting.json`: split statement, unchanged hypotheses and conclusion, seven proof steps. Existing searches retained; new logged searches find no exact Mathlib theorem.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-completed-retraction-conormal-torsion.json`: one new statement-only input, unsplit, no Mathlib match. Its assertion is bounded torsion of the conormal module of a completed retraction, not existence of a lift.
- `citations.json`: a verbatim statement quotation for every citation in every step.

Attachments: none. Searches of the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, the id, Elkik, etale/completion, henselian/completion, completed section/retraction and conormal torsion found no declaration stating the item or the new input. The upstream master is reference material only; no sorry declaration is claimed as a proof.

WANTED: none.

The item is the henselian-target specialization of Stacks 0AKJ, `restricted-lemma-fully-faithful-etale-over-complement`. I read its statement and complete proof at `literature/stacks-project/restricted.tex:1847–1907`, including the base change to C, the conormal argument, 0ALR, and the final etale-neighbourhood argument. I read 0ALQ (`lemma-rig-etale`), 0ALM (`lemma-exact-sequence-NL`), 0ALR (`more-algebra-lemma-quotient-by-idempotent`), 0A43 (`more-morphisms-lemma-check-smoothness-on-infinitesimal-nbhds`), 05GG (`algebra-lemma-hathat-finitely-generated`), 00IQ (`algebra-lemma-intersection-powers-ideal-module`), and 0ALJ (`more-algebra-lemma-complete-henselian`) at their labels. The statement of 0AKJ agrees with the imported item when the target pair is henselian. No STATEMENT-DISPUTED correction is needed.

The item had no proof. I kept its statement and definitions. A possible C4 error in a naive use of the existing 0ALR node is that algebraizing over C alone would forget the required map from E. Step 3 instead applies that node with both its base and its input algebra equal to E. Its stated conclusion is an E-algebra isomorphism, which supplies exactly the compatibility needed later. The source also shrinks an algebraization to make it etale away from the ideal; for this specialization the etale open around the full closed fibre alone gives an appropriate principal localization, so that extra assertion is not needed.

Nothing remains unfinished in the split. The new input is deliberately unsplit, as required by the one-level delivery contract. No Lean was written, compiler invoked, live file changed or agent started.

## Not duplicates

lem-per-completed-retraction-conormal-torsion vs lem-per-etale-away-completion-hom-lifting: the new assertion only bounds the conormal module of a completed section. It constructs no algebra map into an uncompleted henselian ring and assumes no henselianity. Steps 3–7 still algebraize, construct an etale neighbourhood, lift, verify the completed map and prove uniqueness.

lem-per-completed-retraction-conormal-torsion vs lem-per-completed-etale-jacobian-torsion: the latter assumes a complete base and a finite module algebra, and gives the torsion kernel and cokernel of a completed polynomial presentation differential. The new assertion has an arbitrary Noetherian base and finite TYPE source with a specified completed retraction; its conclusion concerns that retraction's kernel modulo its square.

lem-per-completed-retraction-conormal-torsion vs lem-per-elkik-finite-etale-away-completion: the latter is an equivalence between categories of finite algebras over a henselian pair and its completion. The new assertion is a conormal bound without finiteness as a module, henselianity, or an equivalence. Citing Elkik for this would also reverse the existing dependency route.

I searched the whole DAG for 0AKJ, 0ALQ, 0ALM, conormal torsion, completion retractions and completed sections; these three files are the only existing nodes carrying the new source's tags. I also read `lem-per-conormal-torsion-algebraization`: it assumes the conormal bound and does not prove it. `lem-per-completed-differential-finite-conormal` concerns a complete local algebra over a coefficient subfield and does not cover this general situation. Whole-blueprint `blueprint_refs.py search` queries included conormal, completed section, retraction, 0ALQ, 0ALR and etale completion; none states the new lemma. The ancestor command confirms `lem-per-artin-gabber-affine-curve`, and the new via chain starts with the present item.

## Review by Q53

I reread delivery-errors B–E against the item, the new statement, and the cited node statements. The unit `sk-p-dl-a1-perverse` and chapter `sec-deligne-laumon-a1` were read; the current main-20261015 ancestor statement and proof were read as well. This is the already recorded duality/partial-algebraization/Elkik support branch. Neither the unit route nor the unit realization is changed. The historical Step 3 duality clause and the current ancestor's duality input are the provenance, not a claim that the blueprint contains this commutative-algebra calculation. The generic off-unit inputs are recorded individually in `split_report.tool_uses` for maintainer review.

Step 1 takes the surjectivity, exact kernels and completeness clauses directly from `lem-weil-pbc-module-completion-complete`; finite generation of I is available over the Noetherian base. The coordinate calculation proves automatic continuity and that agreement on D determines the completed map. It does not assume continuity without justification or finite generation of D as a module.

Step 2 uses `lem-weil-pbc-finite-type-algebra-noetherian` for the tensor-base-changed finite type algebra, and `lem-weil-pbc-etale-scheme-base-change` for the restriction to the inverse image of Spec A minus V(I). The explicit balanced quotient maps construct sigma and prove its retraction identity. C is assumed Noetherian but need not be finite type over A; neither citation requires that additional hypothesis.

Step 3 uses the new statement with R=C, J=IC, S=D tensor C. The map sigma is a completed-base algebra map by its retraction identity, as the new statement requires. The new statement is exactly the conormal conclusion in the A=C existence paragraph of 0AKJ using 0ALQ and 0ALM. It is a real smaller lemma: it contains no existence or uniqueness of lifts. The 0ALR node is applied over E, retaining E-linearity of beta. Extending the annihilating ideal from C to E still annihilates the module, by linearity. The finite-type generators compose, so T is Noetherian by the cited permanence statement.

Step 4 uses the quotient-kernel clause of the completion node on T and C to reduce beta. E-linearity and the retraction identity say that the reduced structural map is the inverse of beta modulo J^n. The infinitesimal-etale node explicitly provides an open W containing the full closed fibre. Its hypotheses hold: both affine rings are Noetherian, T is finite type over C, and every infinitesimal base change is an isomorphism.

Step 5 invokes only the open-immersion and composition clauses of `lem-weil-pbc-etale-composition-cancellation`. The affine closed-set calculation chooses g in 1+JT with D(g) inside W; the displayed finite geometric sum proves its invertibility modulo every J^n. This is the elementary reason localization preserves the completion and the quotient isomorphisms, not an uncited approximation theorem.

Step 6 uses the actual single-stage henselian map statement, `lem-weil-pbc-henselization-stage-map`, twice. The first target is C, the second is its completion. The second target is henselian by the complete-pair node and the completeness already supplied by 05GG. The quotient isomorphism and both ideal conditions are explicit. Stagewise uniqueness proves equality of the two maps from F to the completion, so the constructed u has the GIVEN completion, not merely an abstractly isomorphic one.

Step 7 uses the Jacobson-radical implication in the henselian factorization criterion, then Krull intersection on the rank-one finite module C. It proves injectivity into the completion and hence uniqueness pointwise on D. No localness or excellence of C is used.

For the new input I checked R=S (zero kernel), J=0 (the bound is trivial with c=1), J the unit ideal (both completions are zero), nilpotent J (a sufficiently large J-power is already zero), and a nontrivial ramified algebra R[x]/(x^2-t) over R=k[[t]]. A retraction in the last example requires an actual root, so the new statement does not assert existence of a nonexistent section. For the item, I=0 reduces to the identity completion and arbitrary algebra maps; a unit ideal forces the henselian target to be zero; C=0 is allowed. None of the arguments exclude these cases. The new lemma does not assert that etaleness survives arbitrary localization of the completion outside the ideal; the completed cotangent torsion input is precisely what is needed.

I read the logged Mathlib hits rather than treating service success as a match. The nearest hits in `RingTheory/Smooth/AdicCompletion.lean` lift maps by formal smoothness into complete targets or produce sections of kernel-adic completions. `RingTheory/Ideal/Cotangent.lean` defines the quotient K/K^2 and gives its elementary properties; `Extension/Cotangent/Basic.lean` gives cotangent-complex maps. None supplies the conormal bound from etaleness outside J or the henselian algebraization theorem. Both semantic phrasings, Loogle and source grep are recorded exactly as run in searches.jsonl; no unavailable service is reported as absence. No Mathlib leaf is claimed.

All seven steps are below 2000 characters. The new unsplit node has no proof sketch or proof dependencies in its JSON, every object in it is introduced, and its notions cite their definitions. Every cited statement was opened, and citations.json quotes each verbatim. No SGA route is used.
