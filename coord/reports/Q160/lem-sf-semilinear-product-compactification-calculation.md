# Stage-1 delivery: lem-sf-semilinear-product-compactification-calculation

## Files written

- dag/nodes/sec-six-functors/lem-sf-semilinear-product-compactification-calculation.json: statement, now split into six whole-system adjunction calculations. Existing statement and statement dependencies retained verbatim. Mathlib verdict: no match.
- citations.json: one verbatim statement quotation for every occurrence of a proof-step dependency.
- report.md: this report. Existing write_split.py and searches.jsonl were retained as working history; the item JSON is authoritative.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this is an auxiliary calculation, not the unit's key statement.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id and semilinear compactification/mate terminology found no project declaration proving every clause. General compactification composition declarations do not state this arbitrary-coefficient system identity.

## WANTED

None. All source passages needed are available in the read clone.

## Problems and corrections

The live item had a statement and searches but no proof. The inherited sandbox already contained a six-step draft, citations and five logged searches, without a report. I retained that argument and the logged searches. The current repository statement agrees with the sandbox statement. There is no released repair note for this item.

The imported calculation is deliberately stronger in domain than the finite-coefficient product identity: it concerns ordinary unbounded derived categories of strict semilinear systems, without cartesianness, finite coefficients or constructibility. I do not apply the finite-coefficient product identity as a theorem in this domain. Likewise def-exchange-projection supplies the stipulated words, not a theorem asserting their invertibility here. All functorial assertions needed in the proof are taken from the explicitly whole-system nodes.

I clarified that A is arbitrary in step 1 and equals V_0 afterwards, recorded the proper/open hypotheses when applying the square-mate node, and removed the draft's broad elementary flags from steps 2, 5 and 6: they are applications of the cited adjunction results, with the actual calculation written out. No step exceeds 2000 characters. No new lemma has been hidden by shortening a long step.

## Unfinished work

None within the requested one-level stage-1 split. This delivery writes no Lean and runs no compiler. The dependencies' subsequent formalization remains their own work.

## Not duplicates

No new nodes. Existing open normalization, external coherence, proper/open mates, system operations and abstract adjunction facts are reused. The nearest blueprint ancestor is lem-sf-kunneth-coherence, through lem-sf-integral-open-product-diagram-normalization. Searching the blueprint for compactification found related finite-coefficient statements but no identical arbitrary-system calculation. The place served is the symmetry proof's reduction to proper morphisms by independence of compactification.

## Mathlib search review

I read the inherited item searches and all five rows of searches.jsonl. The first recorded leanfinder query concerned product compactification in unbounded semilinear sheaf systems; its hits concern profinite good products, topological sheaf equalizers and inverse-system limits. The second phrasing concerned projection, extension by zero and monoidal adjunction transposes; it found abstract closed-category evaluation identities and condensed internal Hom identities. LeanSearch returned scheme module restriction adjunctions and unrelated zero-extension/zero-morphism declarations. Loogle's query with mate and tensor and the CategoryTheory grep for compactification/exchange/projection combinations both returned zero hits. None gives the specified six-functor words on system categories or is a one-line specialization proving the item. Existing queries are preserved exactly, with their actual successful/no-match results; no unavailable service is described as a negative result. No new node requires additional searches.

## Review by Q160

I read Stacks sites-cohomology.tex Tag 07A7 (remark-base-change), which defines exchange as the transpose of the pulled-back counit; Tag 0GL1 (lemma-j-shriek-and-tensor), which gives derived open tensor comparison; and Tag 0E48 (remark-compatible-with-diagram), whose projection/base-change compatibility omits the verification. I also read more-etale.tex Tags 0F7C/0F7D (lemma-shriek-proper-and-open-compose and its horizontal variant). Their etale finite-setting proofs motivate the mate convention but are not invoked to assert unbounded pro-etale system coherence. The source is correctly marked agent: this is an explicit adjunction calculation filling that omitted verification. The blueprint passage read was main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, the reduction-to-proper sentence. The proof stays on that route.

For step 1 I opened lem-coef-semilinear-derived-sections: its statement supplies the simultaneous adjunctions and canonical system morphisms, not merely evaluated maps. I opened lem-sf-open-tensor-normalization: its last paragraph explicitly includes arbitrary strict inverse coefficient systems, and its earlier paragraphs specify beta, its restriction and derived full faithfulness. I opened lem-sf-semilinear-proper-open-mate-pasting: it explicitly identifies its first open-restriction isomorphism by right-adjoint conjugation. The Hom chain in the step therefore uses the correct beta inverse. The displayed counit equality follows by the unit/counit Hom formulas stated in lem-weil-pbc-adjunction-of-natural-bijection and the pasting identities actually stated in lem-weil-pbc-mate-pasting. It is proved on the whole system category.

For step 2 the same system node gives the specified exchange as an adjunction-mate word; the abstract mate node gives pasting and the natural-bijection node gives injectivity of transpose. I checked the square equation as=bkr and the type P_r P_bk = P_s P_a. Restricting the a-counit therefore gives exactly the defining exchange for (a,bk). The argument does not assume proper base-change invertibility.

For step 3 I opened lem-sf-semilinear-open-external-coherence. Its statement explicitly says the word through bar X times_B Y equals the ordered e_{j,k}; that clause, not an unexposed part of its proof, gives e=J_i(tau) delta. The normalization node gives the second-factor tensor word by signed symmetry, identity restriction, and full faithfulness. The system node supplies monoidal pullback. P_z(H tensor J_k L) is in the image of J_i because beta sends P_z J_k L to J_i P_r L and open tensor moves the other factor inside. The target J_i J_v D is also in this image. This justifies the only equality test by restriction used later.

For step 4 I checked the actual proper/open node's formula Gamma=(S_p J_k epsilon_r)(S_p alpha S_r)(eta_p J_i S_r), as well as its assertion that this is the open adjunct of lambda inverse. On our Cartesian square the clopen correction is identity, alpha is beta, and r,z are proper base changes of a. Thus the stipulated Gamma in the item really is the mate used in the calculation. The system node states the ordinary projection map as a counit transpose; the natural-bijection node states the triangles and transpose formulas. Substitution and the written cancellation yield the displayed z-transpose, rather than an unspecified comparison.

For step 5 the system node again supplies the counit-defined projection. Restricting the two transposes uses exactly the normalization node's identity restrictions under the canonical pullback/tensor comparisons. The second-factor signed tensor convention occurs on both sides; after restriction both are the same symmetry with its inverse, so the final formulas have the same sign. Their first factors are d and d', equated by step 1. Step 3's full-faithfulness argument applies because both transposes have its supported source and target. The adjunction Hom bijection then proves the original identity. At no point is arbitrary restriction, coefficient evaluation or scalar restriction claimed faithful on Hom sets.

For step 6 I compared the explicit compactified words in the item's statement and def-exchange-projection with the two resulting expressions. The projection for bk is S_b(gamma'_k) Omega. The projection for rv and exchange for aj give the written R. The proper/open node supplies precisely S_b Gamma for the middle composition, and the system node supplies the direct-image compositor. Thus applying S_b to step 5 and composing with Omega gives the claimed equality for lambda. No projection is inverted. This uses definitions and preceding computations, not the finite-coefficient theorem as a black box.

I checked edge cases with j and k identities (the open comparisons, Gamma and e reduce to identities), empty X or Y (both supported objects and composites are zero), and zero K or L. The argument never uses a transition map being flat or an input being cartesian, so nonflat transitions do not alter the typing. No statement correction or source error was needed. I checked delivery-errors B through E: there are no new statement-only nodes to misstate, duplicate or relabel clauses; all cited statements were read, every uses occurrence has a verbatim quote, and the non-elementary work is either an existing cited assertion or the displayed mate calculation. The three off-unit tools declared in split_report are the generic open normalization and abstract adjunction/mate facts; they do not replace the unit's proper-reduction route.

## Resumed dry-run repair

The required first dry run of the preserved split exited with a citation-length failure: three quotations of the open-normalization statement had only 34 characters. I replaced those fragments by its complete open-adjunction, beta/gamma, normalization and diagram-topos passages. I also expanded the system-operation, proper/open-mate and adjunction quotations to include the actual formulas and domain assertions used by the corresponding steps. All quotations remain verbatim substrings of the current live statements. The proof and statement did not change.
