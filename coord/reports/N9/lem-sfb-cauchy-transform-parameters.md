# Stage 1: lem-sfb-cauchy-transform-parameters

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cauchy-transform-parameters.json: split item, original statement unchanged; five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-euclidean-smooth-ball-bump.json: statement, Mathlib leaf (ContDiffBump and its property declarations).
- dag/nodes/sec-six-functors-basics/lem-sfb-locally-integrable-parametric-convolution.json: statement, Mathlib leaf (absolute convergence, smoothness and total first derivative, with every declaration and line in mathlib_match.how).
- dag/nodes/sec-six-functors-basics/lem-sfb-cauchy-green-test-function.json: statement, unsplit; locally integrable Cauchy kernel and reproduction of compactly supported test functions from their antiholomorphic derivative.
- citations.json: one verbatim statement quotation per step/node pair.

## Attachments

None. The required searches under lean/WeilConjectures for the blueprint tag, Cauchy transform, Cauchy--Green, cauchyTransform and dbar gave no relevant project declaration. The dbar hits are unrelated residue-field derivations. Mathlib declarations are recorded as leaves, not project attachments.

## Literature wanted

WANTED: Jean-Pierre Demailly, Complex Analytic and Differential Geometry, I section 3.A, formula (3.2), Corollary (3.4), printed p.21, and I section 8, Exercise 8.5, printed p.61, for lem-sfb-cauchy-transform-parameters and lem-sfb-cauchy-green-test-function. The PDF is absent locally. I read these passages online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf (PDF pages 21 and 61). No download or repository edit was made. The assembly is marked agent-written and the source records local absence.

## Corrections and scope

The imported statement is correct, including its sign and factor 1/pi. No STATEMENT-DISPUTED correction was necessary. The zero extension is globally smooth because the cutoff support is strictly inside D_R. The kernel cannot be differentiated under the integral as an ordinary integrable function; the proof instead differentiates the smooth factor after writing the transform as convolution. This is the partial-convolution route of the source, not a change of the unit's route.

The new Cauchy--Green lemma is a left-inverse identity C(dbar u)=u for compactly supported u, rather than the item's right-inverse assertion dbar(C H)=H with cutoff and parameters. The item derives the latter by the independently stated derivative-of-convolution theorem; neither new analytic node merely repeats the item. No new Stacks result or SGA source is used.

I read the chapter and unit records and the three levels in SETUP.md. The inherited blueprint provenance has from.node=null: tools/blueprint_refs.py ancestor prints None for this item. I preserve this existing provenance and extend its via chain for new nodes, with precise supporting places. Searches in the latest blueprint, rather than older snapshots, found no Cauchy/Dolbeault/convolution node stating these analytic facts. The item is not the unit's key statement, so no realized fields are changed.

## Not duplicates

lem-sfb-euclidean-smooth-ball-bump vs lem-sfb-smooth-subordinate-partition: the latter is a locally finite partition of unity on a manifold, not the specified ball bump with exact compact closed-ball support. The bump is already a direct Mathlib construction; deriving it through partitions is unnecessary.

lem-sfb-locally-integrable-parametric-convolution vs lem-sfb-cauchy-transform-parameters: the new leaf allows any locally integrable kernel and gives smoothing and the total first derivative; it asserts no dbar right inverse and has no cutoff construction.

lem-sfb-cauchy-green-test-function vs lem-sfb-local-scalar-dolbeault: local solvability for closed differential forms does not state the explicit global reproduction identity, kernel normalization, or local integrability. The parent also depends on the item, so citing it would make a cycle.

lem-sfb-cauchy-green-test-function vs lem-sfb-cauchy-transform-parameters: the test-function identity requires u compactly supported and integrates dbar u. The transform produced in the item generally has no compact support. Its right-inverse property is obtained by a genuine additional argument, not applying a reformulation of itself.

Whole-DAG searches for Cauchy--Green, Cauchy--Pompeiu, locally integrable convolution and ContDiffBump found no existing duplicate; blueprint_refs searches for Cauchy, convolution and bump gave no matches. The broad compact-support search returned unrelated sheaf-theoretic nodes, whose statements do not concern analytic convolution. There are no new Stacks tags shared with existing nodes.

## Review by N9

I read Demailly's proof of (3.2): the area form is dx dy, the deleted small circle contributes u(z), and a containing disk has zero boundary term for compactly supported u. Replacing the denominator zeta-z by z-zeta changes the minus sign in (3.2) to the positive sign used here. The same passage explicitly notes local integrability of 1/z, and (3.4) confirms the normalization. Exercise 8.5 uses the one-coordinate cutoff convolution, which is exactly the analytic operation needed by the existing scalar Dolbeault parent. For the new unsplit Cauchy--Green node, the future proof is the containing-disk case of (3.2); local integrability also follows by polar coordinates, where the norm integral near zero is 2 epsilon for 1/(pi w). I leave that node statement-only, as required.

For the bump leaf I read Basic.lean lines 70--74, 137--170 and 203--204, and InnerProduct.lean lines 32--58. The inner-product instance provides HasContDiffBump, the constructor permits arbitrary positive a<b, and the actual theorem tsupport_eq concerns the closure of nonzero support. The finite-dimensional hypothesis gives compactness. Step 1 cites this complete statement, chooses r<a<b<R, and gets both the open neighborhood D_a and compact support strictly inside D_R. This also works in dimension zero for the generic leaf.

For the convolution leaf I read Convolution.lean lines 156--164, 319--325 and 400--406 and ContDiff/Convolution.lean lines 130--148 and 328--338. The locally integrable factor is the kernel; the smooth second factor is compactly supported in one K independent of the parameter. The Mathlib theorem is over the real scalar field here, with complex multiplication as a continuous real bilinear map. Its parameter-first product order is swapped to our complex-first order. The derivative's linear-map-valued convolution, evaluated on a real direction, is exactly the integral displayed in the new statement. No claim of complex differentiability or a global bound on P is used.

Step 2 is local calculus only: product smoothness inside D_R, identically zero near every point outside D_R because b<R, and vanishing of all derivatives off K. This proves all the support and smoothness hypotheses later applications need. Parameter differentiation leaves chi unchanged. It uses no external lemma disguised as a citation.

Step 3 cites the kernel-integrability sentence of the Cauchy--Green node and the absolute-convergence/smoothness sentences of the convolution node. Both are in their statements, not merely their proofs. Substitution zeta=z-w has real Jacobian -I_2 of absolute determinant one, so the convolution is precisely the requested area integral, with the same absolute convergence. A value at its single singular point does not affect that integral.

Step 4 again uses only the convolution node's stated total derivative, in directions 1 and i, and the test-function node's displayed identity. Taking (D[1]+i D[i])/2 differentiates H in the integration coordinate with the positive sign; this is not a derivative of the singular kernel. Each slice H(-,t) really is a globally smooth compactly supported function. The identity therefore gives H(z,t), then chi h and h on the specified disks.

Step 5 cites the same derivative formula for parameter directions and sets up the explicit induction on multi-index length. Every differentiated input remains smooth and has the same compact support, so all hypotheses persist, even when P is unbounded or disconnected. Linearity is finite linearity of absolutely convergent integrals. I checked m=0, empty P, h=0, z outside the cutoff support, and z on the cutoff boundary. No assertion of compact support for the output is made.

I checked delivery-errors B--E: the three new nodes introduce their own objects and analytic meanings, have empty proofs, recorded searches actually present in searches.jsonl, and precise source places; every non-elementary argument has a cited node, with verbatim quotations in citations.json; the split has no dependency back to its parent and does not replace the unit route; all leaf clauses have read declaration references. The five steps are each below 2000 characters (301, 523, 502, 486, 623). I corrected the bump constructor's field-line reference and named implicit center argument after checking the actual source. No Lean code or compiler was used.

## Unfinished work

The statement-only Cauchy--Green prerequisite remains for a later item. There is no unfinished work in this one-level split. Server checks and delivery are run after this report is written.

## Dry-run repairs

The first captured dry run required explicit mathlib_match.line keys in addition to the line references already written in how. I added the verified lines 70 and 333. I also made Lebesgue measurability explicit in the convolution leaf's description of local integrability, so its norm-integrability parenthesis cannot be read as allowing nonmeasurable phases. The corresponding verbatim quotations were regenerated.
