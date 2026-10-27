## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-contracted-prime-tensor-comparison.json (statement, split; not a Mathlib leaf), citations.json, report.md. The item statement, statement dependencies, source, creation record and blueprint ancestry are unchanged. The previously empty proof now has six steps. All steps are below 2000 characters.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. Two existing Mathlib leaves supply the non-elementary input: lem-weil-pbc-localization-tensor-over-base and lem-weil-pbc-localization-tensor-product. Creating another tensor-localization node would duplicate them.

## Attachments

None. I searched lean/WeilConjectures/ for the exact blueprint tag, contracted-prime terminology, and tensor/localization notions. The general derived-cohomology comparison declarations do not state this elementary module result and all its normalization/naturality clauses. No project declaration was found that states the whole item with a finished proof.

## WANTED

None. The necessary source is available locally.

## Existing material and searches

I read Stacks algebra.tex, Tag 05CL (lemma-universally-injective-check-stalks), including both displayed tensor identities and the sentence N_p = N. I also read Tag 00DK (lemma-tensor-localization), Tag 00DL (lemma-tensor-product-localization), and Tag 00D2 (lemma-tensor-with-bimodule); their tags were checked in stacks-project/tags/tags. The source identities are expanded, without changing their hypotheses or claiming a tensor formula alone proves naturality.

The full DAG was searched for these tags, lemma labels, moduleTensorEquiv, and tensor-localization titles. This found the existing general leaves rather than just the narrower away-localization leaf lem-weil-pbc-localization-module-tensor. I read both selected leaves' complete statements. Whole-blueprint searches used tools/blueprint_refs.py with 'localization tensor', 'tensor', '00DK', '00DL', and 'contracted'; no blueprint node states the complete item. The current latest blueprint unit and lem-trf-local-term-locality proof were read. The recorded auxiliary flattening chain is not spelled out in that current proof, but the item is a generic algebra tool already imported on that chain; this split changes neither the unit nor its route. No SGA source is used.

Five fresh searches through msearch.py are recorded verbatim from searches.jsonl: LeanFinder with two phrasings, Loogle for IsLocalization.moduleTensorEquiv, grep in RingTheory/Localization, and LeanSearch. All services answered. I read Mathlib/RingTheory/Localization/BaseChange.lean:34, 68–86, 119–134, 244–264. rTensor at 244 provides alpha's localization input, moduleTensorEquiv at 132 requires both factors already over the localized base, and the tensor-localization instance at 119 provides the generic input to beta. map_lTensor at 256 is naturality in the other variable, so it is not cited as the item's naturality in P. The item remains a split rather than an asserted one-line Mathlib match. Earlier item searches have been preserved.

## Problems found and corrected

No false statement, missing hypothesis or statement correction was needed. The item originally had no proof. The important citation limitation is that the over-base leaf states naturality in N, not P; Step 5 proves the requested P-naturality directly. The over-base leaf only promises A-linearity in its statement; Step 2 upgrades it to A_q-linearity explicitly. No fact is extracted merely from a cited node's proof.

## Review by Q76

I checked the item against Tag 05CL with arbitrary commutative R and A, an arbitrary prime q, and arbitrary modules P and N: no flatness, finite generation or Noetherianity is required. The contracted prime p, rather than an unrelated prime, is essential to the inversion of phi(t). There are no new statements to review.

Step 1 uses the exact fraction relation and operations in def-weil-pbc-module-localization. Primality of p and multiplicativity of both complements are proved from the prime ideal axiom. Mapping a witness u to phi(u) proves the fraction map is well defined; the formulas prove its ring laws. This is a direct definition calculation.

Step 2 uses exactly the general-algebra and arbitrary-multiplicative-subset clause of lem-weil-pbc-localization-tensor-over-base. Substituting its M=P and T=A minus q gives alpha with precisely the required fraction formula. Commutation with invertible multiplication proves the extra A_q-linearity; the leaf is not assumed to assert that stronger scalar claim.

Step 3 uses the full localization criterion (a),(b),(c) stated by lem-weil-pbc-localization-tensor-product, and the ordinary N localization stated by def-weil-pbc-module-localization. Every criterion for the identity on P_q is verified: phi(S) consists of units, denominator 1 represents every element, and witness 1 handles equality. The theorem applies with localized coefficient ring R_p, first localization map id on P_q, and second localization map N to N_p. Its conclusion is exactly that beta is a localization, not yet an isomorphism.

Step 4 uses that same criterion, now to derive bijectivity. The tensor definition's universal property constructs inverse multiplication by each t on X. The equality-witness condition proves injectivity; the fraction-surjectivity condition and commutation of an R-linear map with inverse t-actions prove surjectivity. The last generator calculation proves A_q-linearity. These are short deductions from the cited criterion, not an additional hidden tensor lemma.

Step 5 uses the tensor definition's generator clause and the localization definition's formula for a localized linear map. I evaluated both sides of the actual claimed square on (x tensor n)/s: both give (v(x)/s) tensor (n/1). Finite sums of pure tensors followed by fractions generate the entire source, so no unsupported naturality is imported.

Step 6 uses the same two definitions. If u(t'n-tn')=0, invertibility of u on an R_p-module gives t'n=tn', which proves independence of the proposed inverse delta. Addition, scalars and the two composites follow from the stated fraction operations. Composing with delta on the second factor gives the final square on exactly the same generators. No equality of underlying module types is assumed in place of this canonical isomorphism.

I tested zero modules, identity and zero v, R=A with phi=id, a field base with p=0, R=Z and N=Z/lZ at p=(l) and p different from (l), and already localized N=Z_(l). The torsion module is killed exactly when its annihilator is inverted; this agrees on both sides of beta. Zero divisors cause no cancellation error because Step 1 preserves equality witnesses and Step 6 cancels only elements known to act invertibly. A=0 has no prime, so its case is vacuous; no domain assumption was inserted. Every cited quote in citations.json is a verbatim full statement of its node. Proof dependencies are the union of uses. Both non-elementary inputs are existing Mathlib leaves, so there are no off-route statement citations or tool-use declarations to request.

## Unfinished work

None within the stage-1 assignment. No Lean file was written and no compiler or Lake command was run. Delivery validation is recorded below when completed.
