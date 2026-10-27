1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-resolution-roof-injective-transpose.json: statement item split using existing nodes; no complete Mathlib match.
- citations.json: one entry for each of the eleven step/node citations, quoting each cited statement verbatim.
- searches.jsonl: actual logged Mathlib searches; existing searches in the item are preserved.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained only dispatcher marker files, so there was no earlier split/report/search log to supersede.

2. Attachments

None. Searched WeilConjectures for the blueprint id, resolution roofs, injective transposes, derived adjunctions and mapDerivedCategoryRightDerivedAdjunction. PlusAdjunction.lean has the generic bounded-below adjunction/unit formula, and PlusCompatibility.lean the bounded-below/unbounded comparison, but neither states this item's roof, homotopy, fixed-shift transpose and internal specialization together. They do not justify an ATTACH disposition.

3. WANTED

WANTED: a direct literature statement of this complete internal-invariant roof/shift normalization, for lem-sfb-resolution-roof-injective-transpose. The necessary abstract ingredients are obtained; the assembly is explicitly agent-written, not attributed wholesale to the blueprint or Stacks.

4. Issues in the imported material

The statement is unchanged. The item cited a bounded-below adjunction even though P can be unbounded below. This is harmless for the mathematical statement but would be an incorrect lifting argument: I use the unbounded K-injective Hom bijection with source P. For the canonical transpose, I use the existing unbounded resolving-derived-adjunction-normalization node (all complexes form the resolving class because L is exact). Thus no unrecorded bounded-below/unbounded comparison theorem is needed. The bounded-below adjunction remains among the statement's fixed conventions; its unit normalization agrees with this formula.

The item has a null blueprint.from.node inherited through its creation chain. blueprint_refs.py ancestor reports that fact. The field is preserved, rather than manufacturing an ancestor. The exact inherited from.place already identifies the old roof proof steps 8-9. I read the newest literature/blueprint/latest paragraph (3) and the current unit and chapter: the source gives the open-direct-image route, not the newly extracted abstract calculation. The proof_origin is therefore agent. The dag unit file has historical sec-six-functors metadata while the item is in sec-six-functors-basics; neither record is changed. This is not the unit's key node and no realized fields are changed.

5. Unfinished work

No omitted argument in the item. Existing dependency nodes retain their own stage states. This delivery is exclusively stage 1; no Lean file, repository file or launcher script was written, and no compiler was invoked.

## Not duplicates

No new nodes. Existing bounded-below-injectives-kinjective and kinjective-hom-derived cover the lifting facts; termwise-adjunction-homotopy covers the ordinary transpose; resolving-derived-adjunction-normalization supplies the generic unbounded derived transpose. I also read kinjective-comparison-principle, sc-kinjective-quasi-iso-comparison, sf-kinjective-derived-map-computation and sp-derived-injective-resolution-naturality and did not duplicate them. Whole-blueprint searches for K-injective, injective representatives and termwise adjoint were read: no blueprint node states the whole item. The broad injective-representatives search found supported exterior product and proper base change, neither this statement.

## Review by Q36

I read coord/delivery-errors.md B-E in full and reviewed the actual node statements, not their proofs, against every citation. I read the newest blueprint chapter/unit material and direct-images.proof.md paragraph (3); Stacks derived.tex Tags 070I (lemma-K-injective), 070J (lemma-bounded-below-injectives-K-injective), 070Y (lemma-K-injective-defined), 0FND (lemma-pre-derived-adjoint-functors-general), 0DVC and 09T5 (derived adjunction); and the Mathlib KInjective and Derived/Adjunction source hits. No SGA source is used. No new node needs a source or a separate mathematical review.

Step 1 uses exactly the existing bounded-below-injectives-kinjective statement for J=I[q], whose terms are injective and whose lower bound is -q, and the kinjective-hom-derived statement for its surjective and injective Hom maps. The latter explicitly permits every source complex, so it applies to P as well as LX[0]. Equality in D follows by cancelling Q(e); injectivity gives the required chain homotopy. This avoids requiring P to be K-projective or to have projective terms. I checked the localized equality has target I[q], with a[q] composed after u.

Step 2 uses the termwise-adjunction-homotopy statement, which explicitly gives the chain adjunction and the formula R(h) eta. The source is a single complex; its only component is R(h^0) eta_X. The differential in I[q] at degree zero is (-1)^q d_I^q. Since a sign is invertible, its vanishing is exactly the chain condition from X[-q] to R(I). There is no Hom-complex triangular sign in this operation: shifting an actual chain map shifts components without scaling them. Thus the flat transpose used here is the exact one of the item.

Step 3 checks each hypothesis of the generic unbounded normalization node: both categories are abelian and have the stipulated derived categories, the adjunction is specified, both functors are additive, and the target E has K-injective resolutions by the Grothendieck-K-injective node. Exactness of L gives preservation of quasi-isomorphisms via exact-functor-derived-factorization, so the full homotopy category is a permitted left resolving class. The right-derived-functor definition explicitly provides the universal alpha and its invertibility at K-injectives; this is legitimate data/universal normalization from that statement, not a theorem inferred from a name alone. The normalization node explicitly states Q of the ordinary transpose followed by the right-derived comparison; it supplies exactly alpha_J Q(tilde h), not merely existence of an unspecified derived adjunction.

Step 4 is a short naturality calculation from the cited natural adjunction and alpha. It gives beta at the shifted augmentation as RR(Q(a[q])) inverse times alpha_J. The direction agrees with the item, Q(RI) to RR(N[0]), rather than the opposite comparison. No assertion that R preserves quasi-isomorphisms of arbitrary complexes is used. Invertibility of RR(Qa) follows because Qa is already an isomorphism in D and RR is a functor. This is why the step is elementary relative to the two cited statements.

Step 5 uses the statement of canonical-right-derived-adjunction-shift, which explicitly retains the fixed K-injective shift rather than choosing an arbitrary transported one. In particular I[q] and a[q] compute the shifted derived comparison, so after [-q] the beta in step 4 becomes beta_a. Combined with the explicit component calculation in step 2, this gives the required equality without adding a sign. This is the only non-elementary shift compatibility used. Its stated unbounded hypotheses hold by the Grothendieck-K-injective input already established in step 3.

Step 6 uses the first paragraph of condensed-derived-restriction-calculus, whose statement explicitly supplies Grothendieckness, exact trivial inflation, its right adjoint invariants, and the invariant-inclusion description of the transpose. Factorization through that subobject is precisely the given underived adjunction, and uniqueness is cancellation through its monomorphism. The rest of that large node (cup products and scalar restrictions) is not used. This is a direct specialization, not a separate lemma/node.

For B1-B3 and D1-D4 I checked that no new clauses were relabelled as new nodes, no elementary subclaims were promoted to nodes, and the proof carries the actual assembly. Every source citation has a document/place; formulas use ordinary single TeX escapes in their JSON value. citations.json quotes literal substrings (in fact the whole relevant node statement), and proof_deps is exactly the union of uses. A dependency reachability check found no path back to this item. All steps are shorter than 2000 characters, and no step hides an unresolved comparison. Generic off-unit tools are declared in split_report.tool_uses; no chapter or unit route is replaced.

I tested q=0 (ordinary factorization and no shift), q=1 (the target differential changes sign but the chain-map component does not), identity adjunction (beta_a Q(h[-q]) recovers the localized roof), zero X or N, trivial internal group (invariant inclusion is identity), and an arbitrary nonprojective resolution source. None adds a hypothesis. All a and all h are covered because step 1's localized identity and steps 2-5 depend only on the stated homotopy condition. There is no statement dispute or statement weakening.

Mathlib hits were read, including CochainComplex.IsKInjective.Qh_map_bijective (DerivedCategory/KInjective.lean:41), isKInjective_of_injective (HomotopyCategory/KInjective.lean:133), Adjunction.derived/derived' and derivedη_fac_app (CategoryTheory/Functor/Derived/Adjunction.lean:105), and ordinary injective-resolution Ext/derived-functor candidates. They cover ingredients, already in the DAG, rather than every clause of the item by one-line specialization. Two semantic phrasings were run and recorded exactly. The first narrow grep produced zero hits, and the later wider grep found the expected localization and bounded-below-injective declarations; both results are retained without alteration.
