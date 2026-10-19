## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-global-frobenius-iterate-formula.json: item, statement, split; no exact Mathlib match.
- citations.json: the single proof citation, with the arbitrary-algebra clause copied verbatim.
- report.md: this report. searches.jsonl is the search command's original log.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The existing definition node is already a Mathlib leaf.

## Attachments

None. I searched the read-only slopmaster2 WeilConjectures tree for the exact item tag, Frobenius iteration terms, globalFrobenius/global_frobenius, natural-transformation iteration and transport/power terms. No project declaration states the abstract identity under its general hypotheses. The nearby AlgebraicGeometry.ProEtale.WeilComplex.stalkFrobenius_eq_pow at SixFunctors/ProEtale/TraceFormula/Frobenius.lean:305 has a sorry (line 311) and concerns geometric stalks, not arbitrary categories. It cannot attach this item.

## WANTED

None. This is a direct calculation from the categorical assumptions, not a missing literature theorem.

## Audit and corrections

The item was a statement-only child of prop-trf-karoubi-independence. I read the chapter sec-trace-formula, the unit sk-thm-trace-transport (especially the treatment of arbitrary coefficient morphisms and their iterates), and the current main-20261015 ancestor proof. Its final sentence says Frobenius endomorphisms are transported; the node was extracted to supply the power identity missing from the returned proof. The blueprint does not itself write out this general calculation, so proof_origin.by is agent. I changed no hypothesis or conclusion, no coefficient category, no source or ancestry field, and no maintainer-owned metadata. The original searches remain present; seven searches run in this session are appended with their actual queries and results.

All notions needed here are introduced explicitly in the statement, except the algebra terminology, whose cited definition explicitly includes arbitrary structure maps. No scheme Frobenius, pullback coherence, trace theorem, or invertibility is taken from the geometric ancestor. The actual formula follows just from the assumed naturality, the functor composition law, and induction.

## Searches and reuse

Blueprint ancestor returned prop-trf-karoubi-independence. Searches of the whole imported blueprint for 'natural transport', 'powers of an endomorphism', 'transport.*power|power.*transport|natural.*iterate|iterate.*natural', and 'Frobenius iterates' returned no matching blueprint node. Whole-DAG searches for transport-power, the item's title and the ordered-iterate notation identified the item and its geometric relatives. In particular I opened lem-trf-iterated-weil-cocycle: that statement concerns the cocycle for invertible derived Weil maps, not the general transport-power identity, and the elementary ordered-factor recursion here does not need that theorem. No auxiliary node was created for a recursion, an instance of naturality, or the inductive calculation.

The seven msearch invocations are recorded verbatim in searches.jsonl and appended to mathlib_searches. Both semantic phrasings were read. LeanFinder suggests SuccStruct.ofNatTrans and its iterations, equivalence powers, and Endofunctor.Algebra/Coalgebra.functorOfNatTrans. The successor-iteration facts concern indexed small-object structures, not the present formula. I read Endofunctor/Algebra.lean:35-80 and 145-190: the algebra data are exactly arbitrary maps, and functorOfNatTransComp is composition of change-of-endofunctor functors; it does not compute powers of their structure map. LeanSearch's coe_pow and baseChange_pow facts concern existing endomorphism monoids or linear maps, while Iso.conj_pow requires an isomorphism; none provides the varying-domain composite in this item. Loogle returned no hits for the paired category identifiers and exterior-power naturality lemmas for the second query. Grep found Comma/Over/Basic.lean:398-400, which I read: iteratedSliceForwardNaturalityIso is naturality of an iterated-slice equivalence, unrelated to powers of the structure map. The second grep locates the change-of-endofunctor definitions just discussed. No exact match or one-line specialization was found.

## Not duplicates

No new nodes. The ordered-factor recursions and naturality substitution are proof steps, rather than new nodes duplicating a clause of this item.

## Review by Q41

I read the item against the final sentence of literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md, and against the current extracted statement and ancestry. The statement is already self-contained and true for arbitrary categories, arbitrary G-algebra maps, and a natural transformation C to C composed with G. The source's Frobenius context motivates it but is not an extra hypothesis. There are no new-node source statements to audit and no Stacks or SGA assertion used in this axiomatic calculation.

Step 1 cites only def-weil-endofunctor-fixed-pair-category. I opened its statement: its final sentence explicitly defines the ambient category of T-algebras with an arbitrary theta:T(X) to X. This is the clause used, not its smaller full subcategory of invertible fixed pairs. citations.json quotes that sentence. I checked u_m:G^mK to K and v_m:C(K) to C(G^mK) factor by factor. Applying G to the ordered factors of u_m and prefixing phi gives exactly u_(m+1); appending t at G^mK gives v_(m+1). Those recursions are elementary functoriality and reassociation, not a theorem obtained from the definition's proof.

Step 2 cites no node: the base case is literally F's definition. The naturality equation is a hypothesis of this item's statement. Its substitution is f=u_m, source G^mK and target K, giving t_K C(u_m)=C(G(u_m)) t_(G^mK), both from C(G^mK) to C(GK). This checks the direction of the square and avoids an illicit inverse or transport identification. In particular naturality is not assumed for a morphism with the wrong source object.

Step 3 cites no node beyond the preceding local steps. I checked the induction for fixed K, with m=1 as base and a successor from every m>=1. Substitute F and the induction hypothesis into F composed with F^m, insert exactly Step 2's typed equality, combine the two C-images using the functor composition axiom, and substitute Step 1's recursions. Each equality in the display is justified; the induction is not circular. All three steps are elementary calculations from stated assumptions and definitions, and their lengths are 639, 540 and 724 characters, with no hidden long-step sublemma.

Small cases: at m=1 the two composites each have one factor. At m=2 the essential equality is t_K C(phi)=C(G(phi)) t_(GK), giving C(phi G(phi)) t_(GK) t_K; the m=3 ordered factors are phi, G(phi), G^2(phi) and t_K, t_(GK), t_(G^2K), in the correct directions. For G the identity the hypothesis says t_K commutes with C(phi), so the formula reduces to the usual product-of-commuting-endomorphisms identity without assuming invertibility. A constant terminal functor and zero maps in a category with zero morphisms give the expected trivial identities. An empty source category has no K and hence a vacuous assertion. No m=0 assertion is silently added. The proof nowhere cancels t or phi, and so covers their noninvertible cases exactly as required.

Against B-E: no new statement-only record was polluted with a proof; no duplicate or clause node was created; every non-elementary fact was ruled out by the explicit short calculations; the single dependency's statement says exactly what is quoted; there is no cycle, geometric comparison, added hypothesis, or silent statement correction. The correction made was to replace the missing proof with its complete inductive argument.

## Unfinished work

None in the split. Required server dry run and delivery follow this report.
