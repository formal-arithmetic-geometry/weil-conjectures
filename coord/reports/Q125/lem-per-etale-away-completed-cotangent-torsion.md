# Stage 1 report: lem-per-etale-away-completed-cotangent-torsion

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-away-completed-cotangent-torsion.json`: split item, with four proof steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-type-jacobian-torsion-etale-away.json`: new statement-only dependency; Mathlib search verdict no match.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

None. I searched the read-only slopmaster2 source by item id, blueprint tag, and cotangent/completion terminology; no sorry-free declaration states this item.

## WANTED:

None. The Stacks source is present at `literature/stacks-project/restricted.tex`.

## Not duplicates

- `lem-per-finite-type-jacobian-torsion-etale-away` vs `lem-per-etale-away-completed-cotangent-torsion`: the new node concerns the ordinary polynomial conormal differential of S before completion; the item concerns every restricted-polynomial presentation of its completion B, and also requires Noetherianity, completeness, reduction and presentation existence. The passage between these different complexes is the existing 0GAF homology-comparison theorem, followed by the inverse-limit argument written in Step 3.
- `lem-per-finite-type-jacobian-torsion-etale-away` vs `lem-per-completed-retraction-conormal-torsion`: the latter requires a retraction from the completed algebra to the completed base and bounds its retraction-kernel conormal module; the new node assumes no retraction and bounds the two homology modules of an ordinary polynomial presentation.

- `lem-per-finite-type-jacobian-torsion-etale-away` vs `lem-per-completed-etale-jacobian-torsion`: the new node treats an arbitrary finite-type algebra over an arbitrary Noetherian base and the ordinary polynomial conormal map; the existing node assumes a finite algebra over an already complete base and concludes a completed presentation, completeness, reduction, and torsion.
- `lem-per-finite-type-jacobian-torsion-etale-away` vs `lem-per-jacobian-torsion-etale-shrink`: the new node proves etale-away-from-I implies ordinary Jacobian torsion; the existing node proves the converse implication from completed torsion to an etale localization.
- `lem-per-finite-type-jacobian-torsion-etale-away` vs `lem-per-completed-jacobian-homology-comparison`: the new node uses etaleness to obtain an ideal-power bound; the existing node only compares ordinary and completed kernel/cokernel modules and has no etale hypothesis or torsion conclusion.

## What was wrong or corrected

The imported item had no proof and its seeded dependencies omitted the ordinary finite-type Jacobian argument and the completion homology comparison. I retained the statement and added those dependencies. The proof now distinguishes the ordinary presentation from an arbitrary completed presentation, so it does not incorrectly assume completion preserves kernels or cokernels by tensoring. The completed presentation is chosen using the presentation-existence clause of the existing completed transitivity node. No statement dispute was found.

## Review by Q125

I read the item source entry and the Stacks proof at Tag 0ALQ(1), together with the definitions and presentation/completion passages at Tags 0AJP, 0AJQ, 0AJU, 0AJR and 0GAF. I checked the imported item hypotheses: A is Noetherian, I is an arbitrary ideal, S is finite type, and etaleness is required only over the complement of V(I); the conclusion uses the I-adic completion and the stipulated A-action. I also checked I=0, I=A, r=0, the zero algebra, and a non-etale example such as k[x]/(x^2) over k: the former cases are covered by the same power convention, while the latter does not satisfy the hypothesis.

Step 1 uses finite-type Noetherian permanence, completion Noetherianity, the finitely generated ideal clause in the Noetherian definition, and the completion-mod-ideal theorem. Those statements give exactly that B is Noetherian and IB-adically complete and identify B/IB with S/IS; finite type descends through the displayed polynomial quotient. Step 2 uses finite presentation of S, the new ordinary Jacobian-torsion node, and the presentation-existence clause of completed cotangent transitivity. I read the full statements of each cited node and verified that the ordinary node supplies both kernel and cokernel bounds for the chosen presentation, while the transitivity node supplies an arbitrary restricted-polynomial presentation of B. Step 3 uses the existing 0GAF comparison, whose statement explicitly identifies the completed kernel and cokernel with the inverse-limit completions of the ordinary ones. Since each ordinary module is killed by I^c, every quotient in its inverse system is killed by I^c, so the inverse limit is killed as well. Step 4 checks that the comparison's d_beta is precisely the continuous partial-derivative map in the item and that the conclusion therefore holds for every presentation. I corrected the initial plan to avoid claiming that tensoring preserves kernels; the comparison node is cited instead. All uses and proof_deps agree, and every citation quote is copied verbatim into citations.json.

On resumption I compared the sandbox against the current repository: the item remains unsplit there and its statement has not changed. The initial dry run required the two additional same-tag comparisons above; after opening both statements, I added their precise distinctions. I also corrected the saved Mathlib grep: its subdirectory had accidentally duplicated the Mathlib prefix, so the old zero-hit result is explicitly not treated as evidence. The new logged RingTheory grep locates Algebra.etaleLocus_eq_compl_support (Mathlib/RingTheory/Etale/Locus.lean:58), formal etale cotangent vanishing (Etale/Basic.lean:47–49), and Ideal.isTorsionBySet_cotangent (Ideal/Cotangent.lean:113). I read those source passages; support descriptions still require the finite-module annihilator argument, and the last declaration concerns the relation ideal rather than the base ideal. A second semantic phrasing and a valid qualified-name Loogle query also gave no full match. The polynomial-ring definition is now explicitly cited in the new statement. In Step 1 I wrote out why IS is finitely generated, so the completion-mod-ideal theorem is applied to the ideal it actually requires. No proof step exceeds 2000 characters, and no source or route uses SGA.
