# Stage-1 delivery: lem-sfb-one-variable-purely-inseparable-subfield

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-one-variable-purely-inseparable-subfield.json: statement item, now split into four steps; no exact Mathlib match for the full statement.
- citations.json: verbatim statements for every proof-step citation.
- report.md: this report. searches.jsonl contains the five actual wrapper searches; the sandbox's write_split.py is only a local preparation script.

There are zero new nodes and zero new Mathlib leaves. All non-elementary ingredients were found in the existing DAG, so none is restated as a new lemma. The original statement, citations and search history are retained. New searches supplement the inherited searches.

## Attachments

None. I searched the live WeilConjectures source for the exact blueprint tag and for purely-inseparable subfields, power-subfields, p-rank and Frobenius degree. The project PurelyInseparable.Basic file has elementwise criteria, not this classification. No project declaration states every clause of the item.

## WANTED

None. The Stacks files needed for this argument are present.

## Problems found and corrected

The item had a statement and searches but no proof. There is no statement dispute: all hypotheses and both conclusions are retained. In particular, equality is in the given ambient field L, rather than an abstract isomorphism. The direct proof avoids confusing the exponent of an arbitrary purely inseparable extension with its degree, a distinction essential in transcendence degree greater than one.

The current blueprint's direct-images proof is under main-20261015/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md (its front matter names det-thm-sf-ctf-stability-direct-images). Its step (3) assembles the direct-image argument; the item's inherited ancestry records the auxiliary alteration/high-genus curve argument. I preserved that ancestry, including its null from.node, exactly as the ancestor command returned. This auxiliary item neither realizes the unit's whole statement nor changes its route, so no unit record is edited.

## Not duplicates

No new nodes. Searches of the whole DAG and blueprint for purely inseparable extensions, function fields, p-bases and power subfields found the existing tools reused below. In particular I did not create a field-model node overlapping lem-trf-algclosed-curve-model, a p-rank node overlapping lem-sfb-smooth-curve-function-field-p-basis, or a tower node overlapping lem-weil-pbc-purely-inseparable-pth-root-tower.

## Mathlib searches

All five wrapper queries in searches.jsonl ran successfully: LeanFinder for the full statement, Loogle for IsPurelyInseparable and IntermediateField, grep for degrees of powers/Frobenius in FieldTheory, LeanSearch for the power-subfield classification, and a second LeanFinder phrasing in terms of p-rank. The exact query texts and actual hit lists are recorded in the node. I read PurelyInseparable/Basic.lean:322-345: IsPurelyInseparable.finrank_eq_pow gives only a degree p^n, without identifying the subfield. I also read PerfectClosure.lean:350-405: the basis-power and minpoly results there assume separability and keep different scalar data, so they do not directly prove this item. The inherited searches already reached the same conclusion and are preserved.

## Review by Q139

I read Stacks curves.tex Tags 0CCX (lemma-purely-inseparable) and 0CCY (lemma-inseparable-deg-p-smooth) in full, and their combination in 0CCZ. The first explicitly reduces to a degree-p field tower; the second computes the Frobenius-image degree and concludes equality by degrees. I checked fields.tex Tag 09HI, including its degree-p root presentation, and Tag 09G9's multiplicativity statement. For the model and p-basis tools I read curves.tex 0BY1 and 0BY3 and more-algebra.tex 07P2. All tags were checked in the local tag table. No SGA source is used.

Step 1 uses the statement of lem-weil-pbc-purely-inseparable-pth-root-tower, which explicitly supplies generators, the relation alpha_i^p in the preceding field, and every degree p. Its characteristic and finite-purely-inseparable hypotheses are exactly those of the item. Positive characteristic is prime by the zero-divisor argument written in the step. Each intermediate field is finitely generated over k by the original E-generators and finitely many alpha's; no unquoted finite-generation descent theorem is needed. The definition node for purely inseparable extensions gives an elementwise p-power polynomial for every element of F_i, proving algebraicity over E. The statement of lem-kun-transcendence-degree-tower then gives transcendence degree one. I corrected an initial formulation that might have implicitly used finite-implies-algebraic by writing this polynomial explicitly instead.

Step 2 uses only the existence clause of lem-trf-algclosed-curve-model. Its statement explicitly gives a smooth proper integral dimension-one model for a finitely generated one-variable extension over an algebraically closed field; all these hypotheses were verified in Step 1. This is a generic tool from another unit, declared in split_report.tool_uses; the same-unit intermediate-field-realization node assumes curves already exist and cannot supply this clause. The statement of lem-sfb-smooth-curve-function-field-p-basis then gives degree p over the power subfield. Properness is allowed although not required by that tool. Transport is not hidden: the step writes theta(x^p)=theta(x)^p and explains spanning and independence after applying theta and its inverse. No curve-map/Frobenius factorization theorem depending on this item is cited.

Step 3 uses the degree-p root relation furnished in Step 1, writes the rational-expression pth-power calculation for every element, and proves F_i^p is contained in F_{i-1}. Characteristic-p binomial expansion is elementary. The statement of lem-weil-pbc-field-degree-multiplicativity gives precisely the product of the two degrees for the actual inclusions; its finiteness hypothesis for the intermediate field follows because it is a subspace of the finite-dimensional space supplied by Step 2. Cancellation of the positive integer p gives dimension one, and the step explains why 1 then spans. This is a few-line application of the cited theorem and preceding constructions, marked elementary, not a new clause-node.

Step 4 spells out a downward induction with base F_r=L and inductive transition (L^(p^j))^p=L^(p^(j+1)). It gives equality of subfields, not just isomorphism. Repeated degree multiplication, from the cited node's actual statement, gives p^r. The empty tower r=0 is handled explicitly. Every citation is copied verbatim into citations.json; every cited node statement was opened and read. The generic degree-p tower is also declared as an off-unit tool: it is exactly the field-theory tool called by 0CCX, not a change in route.

I checked small cases: E=L gives r=0; k(t)/k(t^p) gives r=1; and k(t)/k(t^(p^2)) gives r=2 with the intermediate k(t^p). Perfectness is used through the curve p-basis theorem over algebraically closed k, not assumed of L. In two variables an exponent-one extension may have degree p^2, illustrating why the dimension-one input cannot be omitted. I checked that the cited dependency closure does not reach the item. Every proof step is shorter than 2000 characters; there is no suppressed long-step lemma. New-node form and duplication checks are vacuous, and the argument meets delivery-errors B--E without moving its conclusion into a new node.

## Unfinished work

None within this stage-1 item. The existing cited unsplit lemmas remain their own queue items; they are not silently proved or modified here. No Lean file was written and no compiler or build tool was run.

## Repair of returned delivery (2026-10-23)

The return names branch head `ba64588c949` and reports a side completion that was never promoted into the live DAG. I continued the retained four-step split and its search history rather than copying the current empty proof over it. The initial required dry run rebuilt the delivery on the current server DAG and passed (`f7c61a8a78b`, not pushed). The current read mirror still has status `unsplit`, no proof and no review for this item; its statement, statement dependencies, source and blueprint ancestry agree exactly with the retained version. There is no released repair note and no newly available project attachment.

I re-read every current proof dependency: the degree-p root tower and purely inseparable definition used in Step 1; the transcendence-degree tower and algebraicity clause used in Step 1; the existence clause of the algebraically closed curve-model node and the degree-p conclusion of the smooth-curve p-basis node used in Step 2; and the finite degree multiplication statement used in Steps 3 and 4. Each full statement still agrees verbatim with the quotation retained in citations.json, so none requires a citation replacement or a different proof route. The tower is Lean-closed and the degree and transcendence-degree tools are available in the current DAG. The curve model still requires precisely finite generation and transcendence degree one over algebraically closed k, all proved before its use. The p-basis node still requires a smooth integral curve and prime positive characteristic, also supplied before its use.

I repaired Step 3 by writing out why the powers form a subfield and why the intermediate space is finite-dimensional: independence in the intermediate field implies independence in the ambient p-dimensional space. The upper degree comes directly from Step 1, so both hypotheses of the multiplication node are now identified explicitly. This preserves the approved mathematical argument while making the finite-degree application unambiguous. I re-read Stacks 0CCX, 0CCY, 0CCZ, 09HI, 09G9, 030H, 0BY1, 0BY3 and 07P2 and the current blueprint direct-images paragraph (3). The equal-field case and the one- and two-step rational-function examples remain valid; every step remains shorter than 2000 characters. No new nodes, searches, statement changes or Lean files are needed. The final dry run and push rebuild the changed proof and report on current sheaf-dag through the authorized delivery tool; promotion and independent review remain the maintainer's operation.
