# Q118 stage-1 report

Item: lem-trf-scheme-galois-comparison-normal-form. Direct delivery, 2026-10-22.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-scheme-galois-comparison-normal-form.json: statement, split; no Mathlib match. The statement and its statement dependencies are retained exactly. Six proof steps replace the empty proof.
- citations.json: verbatim statement extracts for every step/node citation.
- report.md: this report. searches.jsonl contains the five newly executed searches, with their actual results. write_split.py is a sandbox-only drafting script.

New nodes: 0. New Mathlib leaves: 0. No unit realization file is required: this item is not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag and the comparison/Frobenius notions. The tag has no declaration. SixFunctors/Etale/Derived/AdicFrobenius.lean discusses the comparison in implementation notes but takes data directly relative to geometric Galois Frobenius; it does not prove the pro-etale comparison and all its clauses. Other Galois comparisons concern different objects. Hence no ATTACH claim is made.

## WANTED

None. All sources needed here are present. No SGA source is used.

## What was wrong or missing

The imported item had a statement and searches but no proof. The source's sentence that relative Frobenius maps compose does not by itself spell out the comparison between the specified multiplicative iterate and the single exponent am trivialization. This split supplies that calculation. The statement itself needs no correction: there is no STATEMENT-DISPUTED claim.

In particular I did not cite the proof of prop-trf-scheme-galois-comparison as though its statement gave the displayed normal form. Its statement supplies the specified comparison and the multiplicative-iterate property. The m=1 normalization is fixed in the item's own hypotheses and agrees with the source's displayed construction; multiplicativity of the candidate normal forms is proved here.

The upstream item already carried Mathlib search records. I retained these and appended five searches actually executed through msearch.py: LeanFinder with the full comparison statement, Loogle with "frobenius", "pullback", grep for scheme/Galois or trivialized Frobenius in Mathlib/AlgebraicGeometry, LeanSearch with the multiplicative normal form, and a second LeanFinder phrasing emphasizing pullback naturality and exponent addition. All services answered. I read all returned hits and checked Modules/Sheaf.lean:241 (structure-sheaf module pullbackComp) and FieldTheory/Perfect.lean:150–157 (ring Frobenius equivalence addition). Neither has the relevant coefficient/site objects. The regular-category Frobenius result is a subobject pullback theorem, not a scheme Frobenius comparison. No Mathlib match was found.

## Not duplicates

No new nodes. I searched the whole DAG and blueprint for Frobenius, multiplicative comparisons, scheme and Galois, pullback composition, and compositor/coherence statements. I reused lem-trf-derived-pullback-coherence and lem-trf-constant-coefficient-composition rather than creating a new compositor lemma; I reused lem-pur-frobenius-trivialization-pullback rather than creating a naturality or exponent-addition lemma. The existing comparison proposition does not explicitly state this normal-form equation; its statement is not substituted for the argument.

## Review by Q118

I read the chapter sec-trace-formula, unit sk-p-trace-coeff, and the current main-20261015 source prop-trf-scheme-galois-comparison.proof.md in full. Its first paragraph defines the comparison by canceling absolute Frobenius; its second paragraph requests exactly the iterate compatibility checked here. I also read lem-trf-absolute-frobenius-site.proof.md, and the actual Stacks source more-morphisms.tex, Tag 0F6W, label lemma-relative-frobenius-weakly-etale, and sites-cohomology.tex, Tag 0D6D, label lemma-derived-pullback-composition. The first is an isomorphism theorem for relative Frobenius on weakly etale objects, not a bare topological invariance claim. The second describes the actual compositor on K-flat complexes. The extension to natural trivializations and their laws is taken from existing DAG statements, not attributed verbatim to Stacks. No new-node source needs review because none was created.

For step 1 I opened def-weil-finite-field-q-elements, def-weil-finite-field-fiber, and def-weil-scheme-characteristic-p. The first explicitly says the field has characteristic p; the second gives the structural base-change morphisms; the last defines characteristic by p vanishing on every open. Sending p through the structure maps proves exactly this condition, so the step is elementary and also handles the empty scheme.

For step 2 I opened def-weil-absolute-frobenius-scheme, prop-trf-frobenius-factorization and def-trf-scheme-frobenius. They respectively identify q-power Frobenius with the a-fold absolute iterate, state BOTH factorizations at every positive exponent, and define the arithmetic and geometric maps through sigma and its inverse. Cancellation and the displayed affine tensor formulas prove both required factorizations for Phi. Commutation of H_n with g^m is the elementary consequence H_n=H_1^n. This uses no k-linearity of the geometric Galois morphism.

For step 3 I opened prop-weil-pbc-proetale-constant-ring-map, lem-trf-constant-coefficient-composition, lem-weil-pbc-proetale-derived-pullback-composition and lem-trf-derived-pullback-coherence. Their statements give respectively the coefficient isomorphism, its composition equality, the normalized derived compositor, and its explicit associativity equation. All allow arbitrary finite commutative R and arbitrary scheme maps. I therefore did not cite pur713-def-pullback-comparison, whose own coefficient setup is narrower. Reparenthesizing the finite composites by repeated application of the stated associativity equation supplies the comparisons actually used later.

For step 4 I opened lem-trf-absolute-frobenius-site, lem-pur-frobenius-trivialization-pullback and prop-trf-scheme-galois-comparison. The first gives the canonical trivialization and iterations; the second explicitly specifies the same trivialization by relative Frobenius on site objects and states its termwise derived realization for arbitrary finite R. The third states a multiplicative comparison on exactly these pro-etale categories. Only its multiplicative-iterate assertion is invoked, never a supposed normal-form sentence absent from its statement. The base equality is the specified normalization in this item's statement, unpacked according to the source construction. Defining beta_r as the displayed two-arrow composite is a step, not a new lemma or node.

For step 5 the same naturality lemma's statement explicitly includes both the equation with the compositor for uF_X^b=F_Y^bu and the addition-of-exponents equation. I verified its hypotheses with u=g^m: both schemes are X of characteristic p, the map is an underlying scheme map, R is finite commutative, and the coefficient identifications are the canonical ones already checked in step 3. Its b=1 and b-fold-iterate normalization sentences identify its tau with the tau requested here. Thus this step does not attempt to derive naturality under g from the weaker restriction-to-opens clause of lem-trf-absolute-frobenius-site.

For step 6 I checked the domains of every transformation: e_{m,n} has source G_m P_n and target P_n G_m, t_m is evaluated on G_m P_n G_n K, and its naturality is applied to e_{m,n,G_n K}. First naturality also moves G_m(d_n) past t_m when expanding T_nK. The two ensuing arrows are t_m at P_nG_mG_nK and t_n at G_mG_nK, precisely in the order required by the addition law. The factorization and canonical compositor associativity identify this expanded domain with the single d_{m+n}. I then wrote the induction with base 1 and successor (r,1), using the multiplicativity stated by the comparison proposition. This is a calculation of the desired equality, not a citation of a new node restating it. I added the explicit first naturality move during self-review so that the suppressed d_n expansion is accounted for.

I checked B–E of delivery-errors point by point. There are no new statements hiding proof sketches, no new duplicate or elementary nodes, no changed definitions or coefficients, no unsupported source-as-node citations, and no invocation of a cited node's proof. Every uses entry has a verbatim statement extract in citations.json. The ordinary unbounded derived comparisons are used throughout, with no boundedness, constructibility or K-flat hypothesis on K. Small cases checked were m=1 (the normalization itself), m=2 (the first induction step), a=1, the empty scheme, the zero coefficient ring, X_0=Spec(k_0), and a nonreduced affine X_0. The affine factorization remains valid with nilpotents; no perfection of X or etaleness of absolute Frobenius is assumed. All steps are below 2000 characters and the explicit equation calculation hides no additional mathematical input.

The item remains in its original coefficient-change unit and follows its specified Frobenius route. The split_report declares off-unit tools for characteristic/finite-field definitions, scheme Frobenius factorization, the generic pro-etale compositor and its coherence/constant-coefficient law, and the arbitrary-scheme pullback naturality of Frobenius trivialization. These supply generic interfaces that the coefficient-change unit does not replace. No route change is proposed.

## What could not be finished

Nothing mathematical remains for this one-level split. Maintainer review and later proofs of existing open dependencies remain their normal tasks.
