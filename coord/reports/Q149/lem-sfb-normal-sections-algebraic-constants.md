# Worker report: lem-sfb-normal-sections-algebraic-constants

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-sections-algebraic-constants.json: statement, split into six proof steps; no exact Mathlib match for the entire scheme statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-element-tower.json: statement, Mathlib leaf IsAlgebraic.restrictScalars, Mathlib/RingTheory/Algebraic/Integral.lean:248; one-line specialization to a compatible tower of fields.
- citations.json: eight verbatim statement quotations, one for every dependency occurrence in the six steps.

## Attachments

No attachment for the item: searched WeilConjectures/ for the exact blueprint tag and for normal sections, algebraic constants and the function-field notions. NormalSectionsFiniteProduct requires locally Noetherian hypotheses and proves a different assertion. The previously recorded closed declaration AlgebraicGeometry.Scheme.exists_germToFunctionField_eq belongs to lem-sc-function-field-sections-glue; read its actual theorem and proof in lean/WeilConjectures/Mathlib/AlgebraicGeometry/FunctionField.lean:86-114 and reused that existing node without restating it.

## WANTED

None. All sources needed for this item's argument are present. The parent's request for de Jong's paper is not needed to prove this standalone relative lemma.

## Corrections and scope

The statement is retained verbatim. There is no statement dispute. The empty proof is replaced by an argument that uses neither properness, finite type, quasi-compactness nor Noetherianity. In particular, normality of the ring of global sections alone would not suffice to put an arbitrary element of k(X) into that ring: k(X) need not equal Frac Gamma(X,O_X). The proof applies integral closedness to each stalk in its own fraction field k(X), and then uses the existing gluing theorem.

Read the chapter, the assigned unit, and the item's original ancestry through the normal Stein constant-field argument. This is the commutative-algebra/normal-section part of that route. The inherited null blueprint ancestor is retained: tools/blueprint_refs.py ancestor prints None. The exact inherited place and via chain are carried by the item and extended for the new leaf. The unit's key statement is not this item, so no unit file is changed.

## Searches and duplicate checks

All Mathlib searches were made through msearch.py and retained in searches.jsonl, including the second natural-language phrasing. Read the semantic hits: for the item they supply fraction-field instances and ordinary rational functions, not the global-section identification; Loogle's integral-closure hits supply only normality ingredients. For the new leaf, LeanFinder returned IsAlgebraic.restrictScalars as well as Algebra.IsAlgebraic.trans; Loogle found the exact elementwise declaration. Read the full declaration at lines 248-271 and its variables at 215-231, and obtained its file and line by the logged directory grep. One earlier grep passed a file rather than a directory and the wrapper printed malformed file fields; that output was not used as source evidence or recorded in the leaf. The directory grep correctly gives Mathlib/RingTheory/Algebraic/Integral.lean:248.

Searched the whole DAG statements and source fields for 0358, 09GI, algebraic-permanence, 09GJ, algebraic transitivity, finite fraction-field degree, stalk embeddings and rational-function gluing. Blueprint searches included integrally closed, algebraic-permanence, transitivity of algebraic, restrictScalars, algebraic element tower, finite global sections and algebraic rational. Reused lem-trf-finite-domain-fraction-degree, lem-sc-integral-scheme-stalks-in-function-field, lem-sc-function-field-sections-glue and lem-weil-pbc-finite-algebra-is-integral. No blueprint statement states the new elementwise transitivity lemma. The two existing nodes whose source metadata mentions 09GJ are compared individually below; neither states the elementwise tower lemma.

## Not duplicates

lem-sfb-algebraic-element-tower vs lem-pod-algebraic-extension-closure-equivalence: the existing lemma constructs an isomorphism between two algebraic closures for an algebraic base extension; the new leaf is elementwise algebraic transitivity for any compatible field tower, with no algebraic-closure objects.

lem-sfb-algebraic-element-tower vs lem-weil-pbc-relative-algebraic-closure-algclosed: the existing lemma asserts that the relative algebraic closure inside an algebraically closed ambient field is algebraically closed; the new leaf has arbitrary ambient field and only transports algebraicity of one element down a tower.

lem-sfb-algebraic-element-tower vs def-weil-relative-algebraic-closure: that node defines the intermediate field of algebraic elements and states closure under field operations; it does not state that an element algebraic over that intermediate field lies in it.

## Review by Q149

I read properties.tex Tag 0358, label lemma-normal-integral-sections, including its polynomial and gluing proof; fields.tex Tags 09GG (lemma-finite-is-algebraic), 09GI (lemma-algebraic-elements), and 09GJ (lemma-algebraic-permanence); and the pinned Mathlib fraction-degree instance at RingTheory/Algebraic/Integral.lean:696-701. The scheme statement is an agent-written relative consequence of these sources, not an assertion that 0358 states it verbatim. For the one new node I checked 09GJ's argument and IsAlgebraic.restrictScalars:248-271. Its field hypotheses supply the no-zero-divisors hypothesis in Mathlib, and its compatible inclusions supply all scalar-tower maps. No separability or finiteness is assumed by this leaf.

Step 1 uses the statement of lem-sc-integral-scheme-stalks-in-function-field, which includes injectivity of section germs and identifies each stalk's fraction field. Therefore the global section ring embeds in E and is a domain. The finite-degree node has exactly an injective map of domains and a finite-module hypothesis; those are the assumptions here. Its finite-dimensional conclusion is applied to Frac R over Frac A, not to the generally larger field E. The finite-algebra-is-integral statement then applies to this field L as a finite F-module and supplies a monic annihilating polynomial for every element of L. Transport through the embedding in E preserves that equation.

Step 2 is elementary and uses no uncited denominator lemma. It lists the coefficient fractions, their nonzero product d, and the polynomial with coefficients e_i=d^(n-i)c_i. Since i<n, n-i-1 is nonnegative; d c_i lies in A by the displayed product formula. Multiplication by d^n therefore gives the claimed monic equation for d a. Dividing the initial polynomial by its leading coefficient is legitimate in F; a nonzero constant cannot annihilate a in the field E, so n is positive.

Step 3 cites the stalk/fraction-field statement, not a definition as a substitute for that theorem. It applies the assumed normality, through the elementwise definition in def-weil-pbc-normal-ring, only after E has been identified with the fraction field of each stalk. The coefficients are germs of the same base functions, so their evaluation in E agrees with step 2. A point where d vanishes in the residue field is harmless: d is not inverted in the stalk; d a itself is integral there.

Step 4 uses the exact statement of lem-sc-function-field-sections-glue with U=X. Integral schemes are nonempty, and step 3 provides membership at every x. That node gives a global representative r of d a. Then a=r/d in Frac R follows directly from d nonzero in A and the stipulated injective embeddings. There is no assertion that all rational functions have a global denominator in R.

Step 5 only assembles the two inclusions already proved; def-weil-relative-algebraic-closure identifies the displayed algebraic-element set with its named intermediate field. Step 6 uses the new leaf with K=F, its intermediate field=L, and M=E. Step 1 verifies L/F algebraic, without assuming E/L algebraic. The leaf is explicitly elementwise, so the given single algebraic element a suffices. Step 5 then places it in L. Every cited statement was opened and its used clause is in citations.json verbatim; no proof-internal construction of another node is used.

I checked delivery-errors B through E against the actual nodes. The new node is self-contained, statement-only, cites the definitions it uses, has the correct 09GJ label and exact declaration/file/line, and is strictly more general as an algebraic tool than the final clause of the scheme item. The item's geometric and denominator argument is present in its own steps, rather than moved to that node. Every step is under 600 characters, so none conceals a long inline sublemma. The only nontrivial geometric gluing is an existing cited theorem. The off-unit gluing use is declared as a generic tool in split_report.tool_uses.

Small cases checked: a=0 permits the degree-one equation and d=1; n=1 gives e_0=d c_0 and no negative exponent; A a field forces all algebraic a to be regular everywhere, so R itself is a finite field extension; a purely inseparable a still has a monic equation and the same denominator computation; X=Spec B for a finite normal-domain algebra recovers the ordinary fraction-field result. The new transitivity statement also permits K=L, L=M, a in L, and inseparable field extensions. The empty scheme is excluded by integrality, not by an added hypothesis. Nothing in the argument uses affine intersections, a finite open cover, or a Noetherian base. There were no prior returned points to repair.

## Unfinished work

None in this split. The new dependency is an exact Mathlib leaf. Final delivery validation and push are recorded by the delivery command.
