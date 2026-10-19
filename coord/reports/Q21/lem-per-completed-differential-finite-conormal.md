# Worker report

Item: lem-per-completed-differential-finite-conormal. Group Q21, 2026-10-19.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-completed-differential-finite-conormal.json: seven-step split, no new nodes, not a Mathlib leaf.
- citations.json: a verbatim statement for every cited node at every step.
- report.md: this report and signed self-review.

The item statement has no mathematical change. I added only the tensor-product definition reference and its statement dependency. All existing statement hypotheses and conclusions, ancestry metadata and searches are retained. The sandbox was initially empty of nodes and reports, so there was no prior split to discard. No delivery command was previously active.

## Attachments

None for this item. Searches by the exact blueprint tag and by completed/continuous differential and conormal notions under /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no project declaration stating it. The exact master source was also searched as reference material, without treating its sorry declarations as finished proofs. The existing dependency lem-weil-pbc-finite-module-complete-over-complete-noetherian already carries the closed declaration finite_module_complete_over_complete_noetherian (WeilConjectures.RingTheory.FiniteModuleComplete:47–74); I reused its node rather than proposing a second attachment.

## Literature and Mathlib

Read EGA IV-1, preliminaries 0_IV 20.7.14–20.7.15 (printed pp.151–152), 20.7.20 (printed p.153), and 21.9.1 (printed p.177), from literature/ega/EGA-IV-1_PMIHES-20-1964.pdf, via sandbox-only pdftotext output. The first proposition reduces finiteness to the residue conormal sequence and finite residual differentials; the second supplies the completed conormal context. I give its exactness directly using the universal property on finite complete modules. This adaptation is honestly marked proof_origin.by=agent. The source's topological differential module agrees here with the adic completion used in the item because squares of open ideals are open; 20.7.15 explicitly says the topology is the ideal-adic topology. The proof below works directly with the item's inverse limit, so does not silently replace it by a different completion.

Read the Stacks algebra.tex statements and proofs at 05GG (lemma-hathat-finitely-generated), 031D (lemma-finite-over-complete-ring), 00RU (lemma-differential-seq), 00EU (lemma-minimal-prime-reduced-ring), and the 00MA/031B finite-module completion context. These support the existing cited nodes. All these citations are already nodes. No source was downloaded and no literature file was changed.

The inherited Mathlib searches were read and retained. Additional real searches ran through msearch.py: LeanSearch for the completed local algebra theorem; LeanFinder for finite completed differentials and, separately, universal continuous derivations of adic algebras; Loogle for KaehlerDifferential, AdicCompletion; grep for completed/continuous Kahler differentials under RingTheory. Their results and exact queries are in the item and searches.jsonl. LeanFinder's KaehlerDifferential.finite was inspected in Mathlib/RingTheory/Kaehler/Basic.lean:433: it assumes EssFiniteType. A complete local algebra such as F[[t]] need not be essentially of finite type over F, so that hit does not attach or close the item. Smooth lifting and square-zero derivation hits likewise do not state this theorem. Both search phrasings were read before declaring no match. There are no new-node searches or leaf claims to validate.

## Blueprint and reuse

Read dag/chapters/sec-deligne-laumon-a1.json and dag/units/sk-p-dl-a1-perverse.json, the current blueprint ancestor lem-per-artin-gabber-affine-curve, and the item's parent lem-per-coefficient-field-generic-differential-basis. This algebra input remains under the existing local-duality/Cohen–Gabber chain; neither the chapter nor the unit route is replaced. The ancestor search returned lem-per-artin-gabber-affine-curve, matching the item's existing from.node. Searches of the whole DAG by completion, conormal, differential, complete Nakayama and minimal-prime concepts located the existing nodes used here. Whole-blueprint searches for completed differential(s), Nakayama, 0315, 00RU, finite-over-complete-ring, module-completion and finite differentials found no equivalent blueprint statement. Therefore same_as remains []. No new node or unit record is written.

The generic complete Nakayama lemma lem-weil-pbc-finite-over-complete-ring is an off-unit tool, declared with its mathematical reason in split_report.tool_uses. Every other proof-level statement used is a Mathlib leaf or Lean-closed. The universal-property proof of conormal exactness is below the unit, not a substitution for the perverse unit's argument.

## Not duplicates

No new nodes. In particular, I did not create a finite-residue-differentials node (the vector-basis calculation is a short step), a completed conormal clause node (that would restate the item), or a second completion/Nakayama/minimal-prime node.

## Corrections and unfinished work

The item was unsplit, with no proof. No statement dispute was found. Its existing reference to 20.7.8 is not used for a quotient-completeness claim: that proposition concerns continuous algebra extensions; quotient completeness here follows from the existing finite-module completeness node, and 20.7.20 gives the correct differential quotient setting. Historical source metadata is retained, while each new proof step gives the actual source place. No part of the requested one-level split remains unfinished; dependencies remain their own existing items. No Lean was written and no compiler, Lake, build, git, or forbidden local checker was run. Delivery uses only the authorized launcher tool.

## Review by Q21

I checked the statement against the EGA passages above, keeping the finite residual extension hypothesis (without adding separability or perfection). EGA 21.9.1 allows a more general finitely generated residual extension, so the finite case stated here is valid. I read every cited node's actual statement, including its explicit strengthened generation clause where used; citations.json reproduces those statements verbatim so an interface cannot be supplied merely by a node's title or proof.

Step 1 uses the Noetherian-ring definition for generators of the maximal ideal and the Kahler definition for the finite vector-basis computation in the residue field. The 00RU node explicitly gives the quotient conormal maps, exact middle term and surjective last map. The displayed calculation with d(sum u_i t_i) supplies the kernel generators after reduction modulo m; lifts of the finitely many d b_j supply the remaining generators. No separability assertion about k/F was used.

Step 2 uses the full 05GG node: completeness and separatedness for an arbitrary module, plus the identification of each quotient of its completion. The hypothesis is finite generation of the ideal, supplied by Noetherianity; no finite generation of ordinary Omega is assumed. The 031D node says not only that the separated completed module is finite but that any lifts of residue generators generate it. Thus the chosen exact differentials really generate algebraically, not merely densely.

Step 3 is the explicit map between compatible sequences induced by the ordinary differential universal property. Linearity sends m^n Omega into m^n N. The assumed completeness of N makes the formula an actual map to N. Checking its values on d_F a proves existence; the exact generators of Step 2 prove uniqueness. No theorem about arbitrary inverse-limit exactness or continuity of an arbitrary derivation is invoked. The argument gives all derivations in the statement. It is a direct limit-coordinate construction for this clause, not a hidden new lemma.

Step 4 uses the finite-module completeness node with A, m and the cyclic A-module A/I. Its statement gives bijectivity of the canonical inverse-limit map, exactly the completeness needed. I verified m^n(A/I)=(m/I)^n, that a proper ideal of a local ring lies in its maximal ideal, the unit criterion for the local quotient, ideal correspondence proving the quotient Noetherian, and injectivity of F in the quotient. These verify every hypothesis before repeating Steps 1–3 for C; its residue field is still k.

Step 5 uses the tensor definition to give both explicit inverses P <-> M/IM. Leibniz supplies the actual well-defined C-linear map from I/I^2, including its vanishing on I^2 and its scalar rule. The quotient Q of finite M is finite by taking the images of its generators. The finite-module completeness theorem, whose hypotheses are unchanged A and m, makes Q complete; the m action is exactly the m/I action. Thus Step 6 has the finite complete target its universal property requires.

Step 6 applies only the already proved universal-property clause, first to C with Q and then to A with M_C. For the latter, finite generation over C implies finite generation over A by lifting coefficients, and the cited finite-module theorem gives completeness. Both factorization conditions, annihilation by I and annihilation of dI, are written explicitly. The composites fix the actual generating exact differentials, so no unproved comparison is concealed behind an identification. This proves the kernel assertion and surjectivity instead of moving that clause to another node.

Step 7 uses the minimal-prime node's explicit assertion q A_q=0 for reduced A, not merely that a localization exists. The fraction identification with Frac(A/q) and the denominator annihilation of each generator of (q/q^2) tensor L are given. The right-exact tensor node states exactly the preservation of an exact sequence ending in zero, which is all that is used; no flatness shortcut is required. The tensor reassociation is exhibited by inverse formulas. The resulting map agrees with the canonical map on each d_F a tensor scalar.

I tested the boundary cases A=k (m=0, reducing to ordinary finite field differentials), I=0 (identity quotient sequence), I=m (including inseparable k/F, where residual differentials need not vanish), dual numbers F[epsilon]/epsilon^2 (including characteristic 2), and a reduced ring with several components such as F[[x,y]]/(xy). In the last case reducedness is exactly what kills q A_q; it was not incorrectly used to make q/q^2 vanish before localization. The empty list of generators causes no step to fail. Every step is under 2000 characters, and none hides a comparison stated as standard. I checked B–E: no new-node packaging issue, no duplicate or circular helper, no missing quoted theorem, no unverified application hypothesis, and no weakened conclusion.
