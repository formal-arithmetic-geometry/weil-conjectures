# Q46 — lem-trf-separable-algebraic-diagonal-localization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-separable-algebraic-diagonal-localization.json`: existing statement, now split into seven steps; the item is not a Mathlib leaf.
- `citations.json`: fifteen verbatim statement quotations, one for every step/node citation.
- `report.md`: this report.

No new nodes or new Mathlib leaves. `searches.jsonl` retains the search command's actual outputs; `prepare.py` is sandbox-only preparation material.

## Attachments

None. I searched the slopmaster2 project by the exact blueprint id, separable-diagonal/localization terminology and multiplication/localization declaration names. `LocallyConstant.isLocalization_lmul'` (WeilConjectures/RingTheory/Spectrum/Prime/LocallyConstant.lean:526) concerns rings of locally constant functions and does not state this item for separable algebraic field extensions. The upstream master is reference material only; its search gave no attachment either.

## WANTED

None: every source needed here is present.

## What was wrong or incomplete

The imported item had the correct statement of Stacks Tag 0C2X but no proof. Its source leaves the finite-case localization calculation as “clear” and finishes the infinite case using exactness of localization. The delivery supplies those missing calculations directly: choose S as the inverse image of the nonzero field elements, reduce each kernel element to a finite separable subextension, calculate its annihilator by a primitive-element polynomial, and prove the induced fraction map is bijective. This is the same primitive-element/finite-support route, without requiring a separate tensor-square presentation or colimit identification. The statement and its statement dependencies are unchanged; no STATEMENT-DISPUTED issue arose.

The item has no Lean audit entry or declaration that supplies a proof. The original Q53 Mathlib searches were retained. Fresh LeanFinder, LeanSearch, Loogle and grep searches were added from the command log. Two Loogle attempts with a literal apostrophe escape were invalid; they are recorded as invalid queries, not evidence of absence, and were followed by the valid query `Algebra.IsSeparable, IsLocalization`. The second semantic phrasing found `Algebra.FormallyUnramified.iff_exists_tensorProduct`, whose source I read: its essential-finite-type/unramified hypotheses and conclusion are not the item. Formal etaleness, flat multiplication, and base change of an existing localization likewise do not state this result. The integral-closure localization theorem concerns a different domain/integral-closure construction. No search result was invented or service failure called absence.

## Not duplicates

There are no new-node pairs. Whole-DAG searches for 0C2X and the mathematical terms, and whole-blueprint searches for `0C2X`, `separable algebraic diagonal`, `localization multiplication`, `primitive element`, and `tensor polynomial quotient`, found no other blueprint statement of the item. The existing finite-separable multiplication-etale node only concludes etaleness/smoothness for finite extensions; the finite-field tensor summand node is restricted to finite fields. Neither is used in place of this proof. Existing general field-theory nodes were reused, including the already duplicated primitive-element interface; no further duplicate was created.

## Review by Q46

I read Stacks `algebra.tex`, lemma-separable-algebraic-diagonal (Tag 0C2X), statement and both proof paragraphs, at lines 10220–10255, together with the adjoining 0C2Y application. I also read the chapter and unit records (`sec-trace-formula`, `sk-i-curve-zero`), the ancestor blueprint text and the current scalar-restriction parent, whose second step needs exactly this localization map. This item fills that existing commutative-algebra input; it does not replace a geometric step of the unit. No SGA source is used. Since this is not a target or a coefficient-category comparison, the exact-target base-change-morphism audit has no additional clause to check.

For the reused field-theory inputs I read their node statements in full and checked their sources: Fields Tag 09GH, lemma-algebraic-finitely-generated; Tag 030N, lemma-primitive-element (the separable moreover clause); and Tags 09G1, lemma-field-extension-generated-by-one-element, and 09GN, lemma-degree-minimal-polynomial. I read the minimal-polynomial/separable-extension and separable-polynomial definition nodes against Fields Tag 09H1, definition-separable, and the tensor, polynomial-ring and fraction definition statements. The source tag/label correspondences were checked in `stacks-project/tags/tags`. No new node needs a separate source review.

Step 1 uses the localization definition only for “multiplicative subset”; the equations showing closure, unit images and surjectivity are written. Step 2 uses the tensor node's explicit generation clause, the separable-extension definition's every-element clause, 09GH for finiteness and the primitive-element leaf for E=k(alpha). All b_i lie in the specified ambient field, are algebraic over the same k, and E inherits separability elementwise; thus both field-theory lemmas have their stated hypotheses. I did not cite the coefficient-specific finite-subextension indexing definition as a general theorem.

Step 3 uses the last sentence of the minimal-polynomial quotient node, which explicitly gives polynomial representatives of every element of k(alpha), not just an abstract isomorphism. Its alpha is algebraic by the extension hypothesis. The separable-extension definition gives P(alpha)=0 and separability. Tensor balancing and the polynomial coefficient formulas justify the displayed F(t)=x calculation, with coefficients in k moving across the tensor sign. These are exactly the statements quoted in citations.json.

Step 4 is the explicit finite geometric-sum identity for T^j-alpha^j, summed coefficientwise; it proves the root-factor calculation rather than hiding an invocation of a factor theorem. Its formula also gives Q(alpha)=P'(alpha) from the derivative definition. Step 5 evaluates the Bezout identity that is literally in the separable-polynomial definition, so the nonzero derivative follows without an uncited preservation-of-separability theorem. I checked that no division by the integer j is used in positive characteristic.

Step 6 evaluates those polynomial identities under the left coefficient map c to c tensor 1, with t=1 tensor alpha. I checked P(t)=0 using p_j in k and the tensor balancing relations; the order of the tensor factors is fixed throughout. Commutativity then gives sx=P(t)H(t)=0 and mu(s)=Q(alpha) nonzero. Only finitely many right factors are needed, so the proof does not assume that an infinite extension has a primitive element, nor that a tensor of injections is injective. Step 7 uses the exact fraction equality criterion stated in the localization node to check well-definedness and zero detection, and surjectivity is the explicit c tensor 1 representative. Thus the conclusion is the actual multiplication map, not an unrelated abstract isomorphism. The elementary flags on Steps 1 and 4–7 correspond to these displayed identities and fraction checks. The only non-elementary applications are Steps 2–3, and all their inputs are existing Mathlib leaves; no off-unit tool declaration is needed. Every step is shorter than 2000 characters and contains no hidden comparison lemma.

I checked B–E against the final files: no new statement-only node, duplicate, item-clause node, source citation masquerading as a node, unsupported hypothesis or circular dependency was introduced. The union of uses is exactly proof_deps. Every node cited was opened and its actual statement was copied verbatim into citations.json. The item's original source, ancestry, citations and search history remain intact; blueprint.same_as is empty after the searches.

Small cases checked algebraically: k_1=k gives the identity after tensor identification and zero kernel; the empty tensor sum uses E=k and alpha=0. For C/R, P=T^2+1, alpha=i and Q=T+i give s=1 tensor i+i tensor 1, mu(s)=2i, killing 1 tensor i-i tensor 1. In characteristic 2, F_4/F_2 with P=T^2+T+1 gives Q=T+alpha+1 and Q(alpha)=1, so the derivative argument still works. An infinite separable algebraic extension such as the algebraic closure of Q uses a finite E separately for each x. Separability is necessary: for the purely inseparable extension F_p(u)/F_p(u^p), the tensor square is L[epsilon]/(epsilon^p), and a nonzero epsilon in the multiplication kernel cannot be killed by a denominator with nonzero multiplication image, because such denominators are units. This is a hypothesis test, not a dispute of the stated separable assertion.

## Unfinished work

None in the requested one-level split. No Lean was written or compiled. Delivery is subject to the required server dry run and push below.

## Validation

The required `deliver.py Q46 lem-trf-separable-algebraic-diagonal-localization --no-push` exited 0 and printed `OK (not pushed)` at f7788d090b: server preflight passed, including the server DAG and split checks. No compiler or local preflight/check_dag/review_split tool was run.
