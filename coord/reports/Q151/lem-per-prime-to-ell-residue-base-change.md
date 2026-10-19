# Worker report: lem-per-prime-to-ell-residue-base-change

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-ell-residue-base-change.json: existing statement split into six steps; Mathlib verdict: no exact match or one-line specialization.
- citations.json: a verbatim statement quote for every dependency of every proof step.
- searches.jsonl: the six searches actually run by Q151, in addition to the inherited search records retained in the item.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves and a closed project theorem supply the algebraic and geometric tools.

## Attachments

None for this item. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id, prime-to-ell terminology, residue base change, residue degrees, coprime degrees and finrank/Coprime found no declaration giving both clauses. The reference master checkout is not used as evidence of a completed proof.

## WANTED

None. I read ILO, Travaux de Gabber, Expose II Proposition 1.2.7, printed pp. 25--26 (PDF pages 31--32), and the relevant local Stacks source.

## What changed and why

The item was unsplit with an empty proof, not a completed interrupted delivery. No deliver.py or msearch.py process for Q151 was running when I resumed; the sandbox contained only brief markers and no previous node, report or search log. I retained the current repository statement, inherited citations/searches and blueprint ancestry. The statement is correct as written: K/k need not be finite or separable, and L/k may be inseparable. No STATEMENT-DISPUTED correction is required.

ILO separates the separable and purely inseparable parts, uses the sum of the field-factor degrees in the etale case, and a power of the characteristic in the radicial case. I use the same degree-sum principle with an ideal filtration of the finite-dimensional tensor algebra. This accounts for multiplicities even when the algebra is nonreduced, and avoids importing two extra field-decomposition lemmas. This is an agent-written expansion below the node, so proof_origin.by is agent, not document. It does not replace any step of the perverse unit route or alter the fixed chapter. Its ancestor remains lem-per-artin-gabber-affine-curve, Step 3, through the inherited alteration-cover-calculus ancestry.

The statement dependencies now explicitly include the existing module-tensor-product and vector-space-dimension definitions. There are no removed assumptions, no weakened conclusions, and no changes to maintainer metadata.

## Search results and reuse

I searched the whole DAG by composition series, finite-dimensional algebra, simple filtration, residue/length, tensor/basis and affine fibre-product terms. I opened the actual statements and sources of the reused nodes. Whole-blueprint searches with tools/blueprint_refs.py for composition series, residue degree and prime to found no alternative blueprint node stating the item; the ancestor command confirmed lem-per-artin-gabber-affine-curve. No new nodes were created, so no tag-duplicate distinctions are required.

The logged searches use the exact queries stored in mathlib_searches. LeanFinder was tried with the original residue-degree assertion and then with the more general finite-algebra dimension formula. LeanSearch, Loogle and two grep queries all ran successfully. Their hits give residue finiteness, linear disjointness, local etale finrank, and length/finrank ingredients. They do not assert that one residue degree is prime to ell in this setting. I read RingTheory/LocalRing/Etale.lean:104: its equality requires an etale local-ring extension. I also read RingTheory/RamificationInertia/Basic.lean:45--85: the ramification/inertia sum is useful algebraic infrastructure, but its translation to this statement is several steps. Neither is an attachment or a one-line Mathlib leaf for this item. Inherited searches remain intact and are not represented as Q151 searches.

## Review by Q151

I checked the source statement in ILO II 1.2.7 against every hypothesis: L/k is finite of degree d prime to ell, K/k is arbitrary, and the conclusion is existence of a residue field with prime-to-ell degree. The additional all-points finiteness clause follows from the finite-dimensional tensor algebra, with no separability assumption. I read the unit and chapter records and the current main-20261015 ancestor proof. This child supplies a field-theoretic input of the inherited finiteness branch; it is not a restatement of the Fourier exactness unit.

Step 1 uses lem-weil-pbc-fibre-product-affine-spectra for the isomorphism and its projection maps, def-weil-affine-spectrum for the one-point spectra and their actual fields, lem-weil-pbc-fibre-product-points for the prime-ideal/point bijection, and lem-weil-pbc-fibre-product-point-residue-field for the fraction-field comparison compatible with both base-field maps. I read all four statements: in particular, the points-only theorem does not supply the residue-field sentence, so that sentence has its own cited theorem. Stacks schemes.tex Tags 01I4 (lemma-fibre-product-affine-schemes) and 01JT (lemma-points-fibre-product), including its last statement sentence, say precisely these things. The comparison is over K, rather than just an abstract field isomorphism.

Step 2 uses exactly the tensor universal property and spanning relations in def-weil-pbc-module-tensor-product and the basis-count definition def-weil-vector-space-dimension. The displayed coordinate functionals show independence as well as spanning, so preservation of dimension under arbitrary scalar extension is proved here, not silently quoted. The K-linearity follows by multiplying the second tensor factor. Only the d-element basis of L/k is used; no finite basis for K/k is assumed. This elementary calculation needs no separate node.

Step 3 applies lem-weil-pbc-finite-dimensional-domain-is-field to A/p. The images of the basis in Step 2 span that quotient; the ideal p is prime and proper, so the quotient is a nonzero domain. These are all the hypotheses of the cited statement. Its field conclusion permits the special field-quotient clause from Step 1, giving exactly the finiteness of kappa(z)/K for every point, with the correct K-algebra structure. The proof does not confuse a local ring or a nilpotent tensor algebra with a field.

Step 4 uses lem-weil-pbc-finite-dim-algebra-artinian on A, then lem-weil-pbc-artinian-ideal-length-one-filtration on the UNIT ideal J=A. I read both node statements: the latter allows any Artinian commutative ring, not just local rings, and explicitly says the quotients are nonzero and have no proper nonzero submodule. I checked Stacks algebra.tex Tags 00J6, 00JB and 00J3 and their labels. The zero length case r=0 is excluded here only because the already proved dimension d is positive. A field extension has d at least one; no zero-algebra case was accidentally admitted.

Step 5 writes out the cyclic-generator proof from Stacks Tag 00J2, lemma-characterize-length-1. Surjectivity follows from simplicity; dividing by the kernel is explicitly bijective, and intermediate ideals would give forbidden submodules, proving maximality. The quotient correspondence is a few-line elementary argument from the preceding simple-filtration statement, not an uncited non-elementary classification theorem. I checked K-linearity in the displayed scalar identity. The use of Step 1 then produces actual points of P and the correct degrees. Since this is elementary and is proved explicitly, I did not create a duplicate simple-module classification node.

Step 6 gives the basis-lifting proof of dimension additivity, then telescopes and applies the elementary divisibility-of-a-sum implication. Thus there is no uncited finite-algebra weighted-degree theorem hidden in the final step. Repeated maximal ideals are allowed and represent multiplicities. Every non-elementary input is in uses and proof_deps; citations.json quotes its actual statement, not its proof or source metadata. No step exceeds 2000 characters.

For B1--B9 and D1--D5 there are no new nodes to check, and no relocation of a clause of the item into a child lemma: the basis, simple-factor identification, dimension sum and divisibility argument all occur in the item. Existing closed/Mathlib tools are reused. The residue-field comparison is also declared as a generic tool in split_report.tool_uses; the unit does not furnish a substitute geometric comparison. I made no source or launcher edits and ran no local DAG checker, compiler or Lake command.

For E1--E6 I tested L=k (one factor of degree one); a separable quadratic extension base-changed to a splitting field (two degree-one factors); an inseparable extension k=F_p(t), L=k(t^(1/p)), K=L (a nonreduced algebra of dimension p with one residue field of degree one and p repeated simple factors); and arbitrary transcendental K/k (the coordinate-basis calculation still works). In the inseparable example ell is any prime different from p, exactly as the prime-to-degree hypothesis requires. The filtration argument retains multiplicities and makes no false assertion that every residue degree is prime to ell. No statement defect or hidden extra hypothesis was found. The main correction to the previously empty proof is that arbitrary K and nonreduced tensors are handled explicitly, with the geometric comparison cited separately.

## Not duplicates

No new nodes. Existing nodes supply every non-elementary tool; no elementary calculation or clause of the item was introduced as a node.

## What remains unfinished

Nothing in the stage-1 split. The mandatory server dry run and direct delivery are performed after writing this report. No Lean proof is claimed.
