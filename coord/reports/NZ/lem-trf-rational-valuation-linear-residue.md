# Worker report: lem-trf-rational-valuation-linear-residue

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-rational-valuation-linear-residue.json`: split item, six non-elementary steps; original shared-base statement restored.
- `dag/nodes/sec-trace-formula/lem-trf-normalized-polynomial-residue-generation.json`: retained new statement-only unsplit node; no Mathlib match. Added the polynomial definition dependency and explicit valuation/residue meanings.
- `dag/nodes/sec-trace-formula/lem-trf-separable-perturbation-factor-selection.json`: retained new statement-only unsplit node; no Mathlib match. Added explicit valuation/residue meanings and removed the construction sketch from the statement.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-inverse-maximal-ideal.json`: new Mathlib leaf, `ValuationSubring.inv_mem_nonunits_iff`, `Mathlib/RingTheory/Valuation/ValuationSubring.lean:571`, with maximal-ideal interpretation at line 617.
- `citations.json`: verbatim statement quotations for all eight step/dependency pairs.
- `searches.jsonl`: retained all previous searches and appended only actual msearch calls. Earlier successful searches were read and reused; the new inverse-criterion searches and results are recorded verbatim in its node.

## Attachments

None. A fresh search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag and linear/transcendental residue notions found no project declaration stating this item. The inverse-criterion theorem is Mathlib, hence a leaf rather than an attachment.

## WANTED

WANTED: local archival copy of Michael Temkin, *Stable Modification of Relative Curves*, arXiv:0707.3953v3, Proposition 4.3.1, proof, printed p. 28 (PDF page index 27), for this item and its two unsplit support nodes. I read the exact source online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including the normalization, polynomial-factor, separable-perturbation and closed-centre paragraphs. No literature archive was modified. The expanded proof is now recorded with `proof_origin.by = agent`, as the unavailable-local-source exception requires.

## Statement restored; earlier dispute retracted

The previous report's claim of a counterexample to the shared-base statement was not established. I retract it. The present item statement is verbatim the current shared base, including its unrestricted closed-centre clause: no algebraic-closedness hypothesis on the residue field is added. The closed-centre argument needs only that the residue of t is algebraic, which follows from the existing Zariski-lemma node, rather than that the centre has a rational residue coordinate. Steps 3–6 prove the original conclusion directly with the very a supplied by Step 2.

There is also a concrete defect in the earlier proposed imperfect-residue example. In characteristic p, for a nontrivial valuation on a separably closed K, lift c from the residue field and choose a nonzero epsilon in the maximal ideal. The monic polynomial X^p + epsilon X - c has nonzero constant derivative, hence is separable and has a root b in K. That root is integral: if b were outside R, its inverse would be in the maximal ideal, and dividing the equation by b^p would force 1 into that ideal. Reducing yields a p-th root of c in the residue field. Thus the proposed c outside its p-th powers cannot occur in that setting. For a trivial constant valuation, the closed-centre hypotheses do not hold. This check invalidates the earlier alleged counterexample; it is not an additional input to the proof.

The sole existing citer is `lem-trf-single-valuation-semistable-extraction`, Step 3, which needs a in R and a positive normalizer for a closed centre. Restoring the original statement preserves exactly that interface. No citer file, target, unit, chapter, or maintainer-owned metadata was edited.

## Repair of each returned point

**A4.** I opened the reviewer-supplied corrected JSON at `reviews/NZ__lem-trf-rational-valuation-linear-residue__f631b4c5f135/fixes/dag/nodes/sec-trace-formula/lem-trf-rational-valuation-linear-residue.json`. The sandbox already retains its correction: `created.item` is this item and `created.group` is NZ. The current shared unsplit base still has the inherited Q87/parent creator record; this delivery intentionally includes the exact correction requested by the return. Historical ancestry through the parent remains in `blueprint.from.via`.

**C1–C2.** I read the entire return review, including its list of four unsupported claims in the old Step 3. That step is gone. Step 3 identifies restriction units and residue embeddings and cites the exact inverse/maximal-ideal Mathlib criterion. Step 4 replaces the uncited maximal-ideal/linear-generator argument by an explicit application of the existing Zariski lemma to E = R[t]/p. Step 5 writes the inverse-ideal and scalar-residue calculation proving a is integral and cites the inverse criterion. Step 6 uses the existing normalization node's previously unused positive-scalar clause, with an explicit residue comparison showing that the new normalization remains transcendental. Every step is marked non-elementary and has actual dependencies. The four steps have respectively 563, 571, 526 and 681 characters; none hides a long comparison argument. Simply changing the old classification was not the repair.

## Not duplicates

- lem-trf-normalized-polynomial-residue-generation vs lem-trf-residual-curve-value-group: the latter normalizes values by constants; the former states field generation by normalized irreducible-polynomial residues.
- lem-trf-separable-perturbation-factor-selection vs lem-trf-residual-curve-value-group: scalar normalization does not select a separable polynomial with transcendental residue.
- lem-trf-normalized-polynomial-residue-generation vs lem-trf-rational-valuation-linear-residue: residue generation by arbitrary irreducible factors does not give the item's linear coordinate or closed-centre integrality.
- lem-trf-separable-perturbation-factor-selection vs lem-trf-rational-valuation-linear-residue: the support node takes an already selected normalized irreducible polynomial and produces a separable one; it does not give the closed-centre refinement. This is the same intermediate node accepted by the previous review, now without a proof sketch in its statement.
- lem-trf-valuation-inverse-maximal-ideal vs lem-trf-rational-valuation-linear-residue: the Mathlib leaf is a generic criterion for one element of any valued field, with no rational-function field, transcendence or coordinate conclusion.
- lem-trf-valuation-inverse-maximal-ideal vs lemma-nagata-composite-valuation-ring: the latter constructs a composite valuation ring from a residue valuation; it does not state the inverse criterion.
- lem-trf-valuation-inverse-maximal-ideal vs lem-trf-valuation-algebraic-height: algebraic-height invariance does not state membership of inverses in a maximal ideal.

The retained two unsplit nodes share the Temkin source with existing modification, Abhyankar and valuation nodes; none states either residue generation or separable factor selection. The former report's pairwise distinctions are preserved below, since the delivery tool may require them for broad source-place matches.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-modification: the existing definition of a modification does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-multipointed-curve-modification: the existing definition of a multipointed modification does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-multipointed-curve: the existing definition of a multipointed curve does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-rational-rank: the existing definition of rational rank does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-schematically-dense-open: the existing definition of schematic density does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-semistable-multipointed-pair: the existing definition of a semistable pair does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-strict-semistable-curve: the existing definition of strict semistability does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-strictly-semistable-curve: the existing definition of strict semistability does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs lem-trf-abhyankar-finite-type-field-height: the existing numerical height bound does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs lem-trf-abhyankar-inequality: the existing numerical Abhyankar bound does not state residue generation by normalized polynomial factors.

- lem-trf-normalized-polynomial-residue-generation vs lem-trf-base-modification-comparison-fibre-image: the existing geometric fibre-image comparison does not state residue generation by normalized polynomial factors.

- lem-trf-separable-perturbation-factor-selection vs def-trf-modification: the existing definition of a modification does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-multipointed-curve-modification: the existing definition of a multipointed modification does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-multipointed-curve: the existing definition of a multipointed curve does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-rational-rank: the existing definition of rational rank does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-schematically-dense-open: the existing definition of schematic density does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-semistable-multipointed-pair: the existing definition of a semistable pair does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-strict-semistable-curve: the existing definition of strict semistability does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs def-trf-strictly-semistable-curve: the existing definition of strict semistability does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs lem-trf-abhyankar-finite-type-field-height: the existing numerical height bound does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs lem-trf-abhyankar-inequality: the existing numerical Abhyankar bound does not state separable perturbation and factor selection.

- lem-trf-separable-perturbation-factor-selection vs lem-trf-base-modification-comparison-fibre-image: the existing geometric fibre-image comparison does not state separable perturbation and factor selection.

The duplicate gate also matched the digits 0707 in the shared Temkin arXiv filename, rather than a Stacks source tag. I opened all three newly listed definitions.

- lem-trf-normalized-polynomial-residue-generation vs def-trf-birational-quasi-modification: the existing node defines birational quasi-modification of schemes and gives no valued-field assertion; the new node states generation of a valued rational-function residue field by normalized polynomial residues.
- lem-trf-normalized-polynomial-residue-generation vs def-trf-centred-valuation: the existing node defines compatibility of a valuation point with a scheme centre and gives no polynomial assertion; the new node states generation of a valued rational-function residue field by normalized polynomial residues.
- lem-trf-normalized-polynomial-residue-generation vs def-trf-nodal-dualizing-datum: the existing node defines a Jacobian-normalized dualizing datum on a nodal family and has no valuation-residue conclusion; the new node states generation of a valued rational-function residue field by normalized polynomial residues.
- lem-trf-separable-perturbation-factor-selection vs def-trf-birational-quasi-modification: the existing node defines birational quasi-modification of schemes and gives no valued-field assertion; the new node states existence of a normalized separable polynomial with transcendental residue.
- lem-trf-separable-perturbation-factor-selection vs def-trf-centred-valuation: the existing node defines compatibility of a valuation point with a scheme centre and gives no polynomial assertion; the new node states existence of a normalized separable polynomial with transcendental residue.
- lem-trf-separable-perturbation-factor-selection vs def-trf-nodal-dualizing-datum: the existing node defines a Jacobian-normalized dualizing datum on a nodal family and has no valuation-residue conclusion; the new node states existence of a normalized separable polynomial with transcendental residue.

## Review by NZ

I compared the retained item and support-node files with both the returned f631b4c5f135 review packet and the current shared base, rather than reapplying an unchanged delivery. I opened the complete six cited statements: the two retained new support nodes, value-group divisibility, residual-curve normalization, the new inverse criterion, and Zariski lemma. I checked the item and both retained new statements against Temkin Proposition 4.3.1 on printed p. 28; I read Stacks Algebra Tag 052K (`lemma-x-or-x-inverse-valuation-ring`) and its proof, Tag 00IB, and the exact Mathlib lines 571, 603 and 617 for the new leaf. I read the Zariski Mathlib theorem at Jacobson/Ring.lean:676 and the existing DAG statement. The chapter and unit remain the recorded historical Temkin branch of `sk-i-curve-zero`; no unit step has been rerouted.

Step 1 uses divisibility for the separably closed ground field, the existing residual-curve lemma for normalization under residual transcendence degree one, and the generation node to obtain a transcendental normalized irreducible residue. I checked L=K(t) is finitely generated of transcendence degree one and that R=O intersection K, so every hypothesis of the normalization statement holds. Step 2 now uses just the stated existence and degree-one clauses of the separable-selection node; I removed the unused normalization citation and the uncited generic-perturbation explanation. The input monic irreducible polynomial and its transcendental normalized residue are exactly Step 1's output.

Step 3 expands units as simultaneous membership of an element and its inverse. This proves R-units equal K intersection O-units, then the maximal-ideal contraction and injectivity on residue fields. The cited inverse leaf states exactly the additional nonunit-inverse assertion used later; its statement includes x=0, so there is no hidden nonzero assumption. Step 4 explicitly makes E a field by the maximality hypothesis, identifies its k-algebra structure using p intersection R = m_R, and checks one-generator finite type before applying Zariski. Its finite-dimensional conclusion gives a polynomial relation by linear dependence. Thus the old uncited assertion about a linear generator of the contracted ideal is entirely unnecessary.

For Step 5 I checked a outside R implies a outside O, because a belongs to K. The inverse criterion puts 1/a in the maximal ideal, multiplication by t remains there, and the sum h+t/a=1 proves h is a unit. Both z and h are units, so z/h is a constant unit and therefore belongs to R-units. Its residue makes z constant, contradicting transcendence. This supplies exactly the missing valuation/residue comparison in the return. For Step 6, y=t-a is nonzero because t is an indeterminate. If y were a unit then pi would be a constant unit and z would lie in finite-dimensional E, which contradicts transcendence by the same linear-dependence argument. Thus y is in m_O, and the normalization node explicitly supplies c in m_R. The ratio pi/c=z_c/z is an R-unit, so the displayed invertible substitution proves preservation of transcendence. This uses the existing node's statement, not its proof. No positivity or equal-value claim remains uncited.

I checked the two retained unsplit nodes against small cases: a trivial valuation, a nontrivial Gauss valuation, irreducible inseparable f, and f of degree one. The selection conclusion remains valid for a trivial constant valuation (choose g=T after normalization); the old sentence promising a nonzero sufficiently small perturbation in every case was a construction sketch and was removed, since the trivial maximal ideal has no such parameter. Both nodes remain statement-only. I corrected their mistaken reference to the field-definition node as though it defined valuation subrings by writing that meaning inline and added the polynomial definition reference. Their existing searches were read rather than invented or rerun.

For the new Mathlib leaf I checked x=0, x outside the ring, x a unit, and x a nonzero nonunit, including the trivial valuation: its equivalence is correct in all cases. The criterion is an exact Mathlib result with the nonunit/maximal-ideal bridge named and read, hence a Mathlib leaf instead of a new elementary unsplit lemma. Searches used msearch only: LeanSearch and LeanFinder identify `ValuationSubring.inv_mem_nonunits_iff`; Loogle gives that exact name; grep gives lines 571 and 617. DAG and blueprint searches by the exact declaration, inverse/nonunit terminology and valuation-subring terminology found no duplicate. Searches of the read-only project Lean source found no project proof of this leaf or of either retained support node. The generic Zariski lemma is reused, with its tool use declared, rather than duplicated.

The item checks include O=K(t), where a=0, pi=1 works and the closed-centre clause fails; the t-adic valuation, whose residual transcendence degree is zero; a scaled Gauss coordinate with positive scale, where the closed-centre conclusion holds; and the proposed imperfect-residue example, whose invalid premise is explained above. Every quoted citation is a literal substring of its node statement; proof_deps is exactly the union of uses; the new nodes have no proof or proof dependencies; the retained searches and historical blueprint ancestry survive. No proof step exceeds 2000 characters. No SGA source, Lean edit, compiler, build, direct git operation, live-project write or agent delegation was used.

## What remains

Only the three delivered support nodes need future stage work: the inverse criterion is already a Mathlib leaf; the two unsplit statements await their own splits. The required server preflight is run before pushing this repair; the initial retained-sandbox dry run passed at 2efa89d267 before these substantive repairs. The Temkin archive request remains open. There is no unresolved mathematical or process repair in the delivered item.
