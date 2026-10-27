# Stage 1 report: lem-sfb-relative-regular-ideal-generation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-regular-ideal-generation.json: item, statement, split into five proof steps; no Mathlib match.
- citations.json: every step/node pair, with a verbatim quote of its supplying statement.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

No new nodes, no new Mathlib leaves, no Lean files. The statement and its statement dependencies are unchanged. The helper write_split.py is sandbox-only and not a delivered project file.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, relative regularity and ideal generation, then Castelnuovo and regularity/generation terminology. The projective-space Resolution module has a special result on P1; it does not give this assertion for arbitrary n or its relative multiplication clause. The project's sorry declarations are not attachment evidence.

## WANTED

None. All the source statements used here are present locally.

## Findings and changes

The item was an unsplit child of the reviewed uniform-section-bound split. It already had correct hypotheses, including actual ideal pullback and canonical geometric-fibre section base change. I retained them all; I did not try to deduce them again or assume arbitrary base change beyond the hypotheses. There was no prior sandbox split/report to preserve and no released repair note.

The independent existing node lem-sfb-m-regular-coherent-sheaf-consequences gives exactly the field evaluation and linear multiplication assertions needed. Thus creating new nodes for 08A6, 08A7 or 08A8 would be duplication. The additional operations are existing general tools, or explicit elementary section and monomial computations. No obligation is relocated into a new copy of the item.

I searched the whole DAG by the regularity tags, regularity terminology, Nakayama, stalk pullback, finite stalks and tensor right exactness; I read the supplying statements. Blueprint searches for Castelnuovo, Nakayama, globally generated and polynomial multiplication found no blueprint statement of this item. The globally-generated hits concern etale constant-coefficient sheaves, which cannot supply Zariski O-module generation here. blueprint_refs.py ancestor reports a null blueprint ancestor for the inherited created-node chain; I preserved it and retained its precise Hilbert-construction place. The current latest chapter and unit text were read, together with the recorded chapter/unit. This remains the inherited Hilbert-scheme prerequisite of the alteration route; no unit or chapter route is changed.

Mathlib searches were run only through the prescribed msearch.py command, using LeanFinder (two phrasings), LeanSearch, Loogle and source grep. All returned successfully. I read the hits: maps on localized Proj chart rings, an abstract free-locus criterion, ideal-sheaf constructors and generic generating-section data are not this result. The exact queries and actual summaries are appended to the item's previous searches. No search is invented and no unavailable service is reported as a negative result.

## Source detail

I read varieties.tex at lemma-m-regular-up (08A6), lemma-m-regular-multiply (08A7), and lemma-m-regular-globally-generated (08A8); algebra.tex at lemma-NAK (00DV), especially parts (4) and (6), and lemma-tensor-product-exact (00DF); coherent.tex at lemma-cohomology-projective-space-over-ring (01XT); sheaves.tex at lemma-stalk-pullback-modules (0098); modules.tex at lemma-abelian (01AG), definition-finite-type (01B5), and the tensor-pullback statement 01CD. For the nonzero-vector-space tensor fact I read the FaithfullyFlat/Basic.lean source named by the existing Mathlib leaf. No SGA source is used.

The proof of 08A8 has a section-degree typo: its chosen sections are written as lying in H0(F), whereas its multiplication argument requires H0(F(m)). I use its correct theorem statement and the existing regularity node's explicitly stated evaluation of F(m). This does not change the item's statement or any supplying node.

## Review by Q118

I checked delivery-errors.md B through E against the finished item and the open source statements. There are no new nodes to audit for self-containedness or duplicate tags; all five steps have explicit source labels, boolean elementary flags, and an exact union in proof_deps. I did not edit existing supplying nodes. Each citation in citations.json is copied directly from the current supplying statement, with no reliance on its proof's internal construction.

Step 1 uses the regularity node's evaluation clause with a=b=m: the geometric-fibre ideal is coherent and m-regular by the item's hypotheses. The tensor-pullback node supplies its natural isomorphism on the actual tensor product. The pullback definition supplies composition, and the twist definition and twist-tensor node supply the local bases and their pairing. I wrote the image of a section times the chart basis, so the comparison is with the canonical evaluation, not with an arbitrary surjection between isomorphic objects. Twists pull back by the identical transition functions. Untwisting is multiplication by an invertible local basis.

Step 2 uses finite-type-module-stalk-finite for I_x and module-stalk-exact for the actual cokernel. Quotients of a finite module are finite by taking images of its finitely many generators. The stalk-pullback node says both the scalar-extension formula and its naturality, and tensor-right-exact gives the cokernel after scalar extension. Choosing an algebraic closure of kappa(x), rather than assuming an algebraically closed residue field, produces a geometric fibre through the specified point. The tensor-nontrivial leaf applies over the field kappa(x), with Omega nonzero, and forces the residue quotient to vanish. Nakayama is applied over the actual local ring O_X,x to a finite module; its statement includes the arbitrary-submodule form, so setting N=0 gives the conclusion. The stalkwise criterion is explicitly a Zariski-topological statement, as required. There is no mistaken appeal to etale geometric stalks and no assumption that an arbitrary tensor pullback is exact on the left.

Step 3 uses exactly the regularity node's multiplication clause for each b=m+r. The twist-cohomology node identifies the linear sections with coordinates; in dimension zero the twist definition gives its single basis x0. The induction starts with multiplication by 1, expands a successor as sum x_i t_i, and collects monomials. This is a routine algebraic induction from the cited surjections, so it is an elementary step, not another regularity lemma. It works for n=0 and has no reliance on a hyperplane choice or on an infinite base field.

Step 4 uses the tensor-pullback isomorphism and the twist pairing on chart bases. Its other inputs are the item's assumed canonical section base-change maps in degrees m and d. I checked that restriction sends x^alpha s to x^alpha times the restricted s, so the base-changed multiplication really is the polynomial map of step 3. The finite monomial basis of V_r pulls back coefficientwise. This comparison is a few-line generator computation and does not hide a base-change theorem for cohomology.

Step 5 uses the same precisely stated stalk, right-exact tensor, vector-space and Nakayama statements as step 2. Here finiteness follows directly from the assumed local finite freeness of K_d. I verified the residue quotient is over kappa(t), not the coordinate ring of the whole fibre. Stalk exactness and the Zariski stalkwise criterion give sheaf surjectivity. The case d=m is multiplication by the degree-zero unit; the empty scheme has only zero sheaves.

I tested the extremes Z empty (I=O) and Z=X (I=0); the relevant fibre maps are polynomial multiplication and zero-target maps respectively. The n=0 regularity conditions are empty and the single-variable induction still proves the assertion. No Noetherian assumption, finite presentation of a cokernel, constant rank, or finiteness of the base was used. All steps are shorter than 2000 characters. The only off-route nonclosed non-Mathlib tool declared in split_report.tool_uses is the generic finite-stalk theorem; the remaining cross-unit inputs are closed or Mathlib leaves. No false statement or missing hypothesis was found and there is no STATEMENT-DISPUTED correction.

## Not duplicates

No new nodes were created. Reused the existing general regularity, Nakayama, finite-stalk, tensor and stalk nodes instead.

## Unfinished work

None in the one-level split. The required dry run and delivery result are recorded below after the tools finish.

## Validation

The required deliver.py --no-push invocation exited successfully: preflight passed, OK (not pushed), at 02e8003c91d on 2026-10-23. Local read-only consistency checks also verified the unchanged statement and statement dependencies, the exact proof-dependency union, and all 22 citation quotes against the live DAG. No compiler, Lake or local preflight/review/check_dag execution was used.
