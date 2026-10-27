# Stage-1 report: lem-sf-common-transition-coefficient-mates

## Files written

- dag/nodes/sec-six-functors/lem-sf-common-transition-coefficient-mates.json — statement item, split into five explicit steps; not a Mathlib leaf as a whole. No new nodes and no new Mathlib leaves.
- citations.json — one verbatim statement quotation for each node cited by each proof step.
- report.md — this report. searches.jsonl was produced by the prescribed msearch.py commands.

## Attachments

None. Searching the project WeilConjectures tree for the exact blueprint tag, common transitions and coefficient mates found no declaration proving the complete item. The general mate calculus is already the existing Mathlib leaf def-weil-pbc-adjunction-mate, so it was reused.

## WANTED

None. The calculation is agent-written from the available common-stage construction and the actual hypotheses of this item. No unavailable reference is needed.

## Findings and changes

The item had an empty proof. Its mathematical statement is retained exactly: in particular the common-stage MORPHISM normalization, rational identity law, actual scalar unitors and counit normalizations are hypotheses, not inferred from object comparisons. The left transition law is obtained by evaluating the arrow formula, and the right law is proved by calculating both counit transposes. No faithfulness of the inclusions, Karoubi completion, ambient exceptional adjoint or separatedness of the schemes is introduced.

The blueprint ancestry field had a null root, and blueprint_refs.py ancestor likewise returned None because the created.item chain ends at a maintenance module, not a blueprint id. The current parent lem-sf-constructible-exceptional-coefficient-coherence explicitly names sk-thm-sf-tensor-hom as its blueprint ancestor. I repaired this item's root to that existing imported node, retained its intermediate parent in via, and identified the third Hom bijection and scalar-extension compatibility as the precise place. The cited exceptional-inverse-image definition supplies the common-stage route. This is a provenance repair, not a change of route.

I searched the whole DAG and blueprint for common-stage transitions, transition cocycles and counits. The existing mate-cocycle node is about a specified geometric exceptional functor and its compositors, with additional finite-field and separatedness assumptions; it does not supply this item's arbitrary adjunction assertion. The parent coefficient-coherence node uses this item and cannot be cited in its proof. Neither is used. The direct calculations are short instances of identity, functoriality and naturality, so making a separate node for either displayed conclusion or their cancellations would be elementary-node duplication or clause relabelling.

The item's original search records are preserved. Five new searches were run with the prescribed command and recorded exactly from searches.jsonl: two semantic phrasings, Loogle, Mathlib grep and LeanSearch. I read all returned hits. The meaningful hit mateEquiv and its counit formula were read in Mathlib/CategoryTheory/Adjunction/Mates.lean, lines 84 and 123–133. They provide the existing mate leaf; they do not state the pair-category transition assertion. The remaining hits concern filtered colimits of modules, filtered indexing categories, Galois systems, monad/comonad comparisons or closed monoidal comparisons and do not state this item.

## Not duplicates

No new nodes were created. No duplicate-node pairs arise.

## Review by Q139

I read coord/delivery-errors.md B–E in both the live and inherited new-target sections and checked the actual node, source and cited statements against their requirements. I read the exceptional-inverse-image construction in literature/blueprint/main-20261015, the master algebraically-closed-coefficient definition, the tensor–Hom sketch and its proof, the chapter and compatibility-unit records, and the parent's normalized construction statement. For the mate definition I read the existing node's entire statement, Mathlib's mateEquiv and mateEquiv_counit implementation, and Stacks Tag 07A7, sites-cohomology.tex, remark-base-change. The latter illustrates counit transposition; I do not attribute the full coefficient calculation to that remark. There are no new-node sources to audit, and no prohibited SGA source is used.

Step 1 cites def-weil-algebraically-closed-coefficients for morphisms represented at a common field. Its statement expressly gives that representation and the equality rule, and the quoted sentence is verbatim. The stronger information about the inverse transition's representative is explicitly supplied by this item's own final sentence. I kept the non-strict identity transition: writing its unitor u, the rational identity equation F(u_X) q_identity = u_Y proves delta_(j,j,A) = I_j F(u_X inverse). This is exactly the factor needed for the stipulated representative, not an unjustified identification of all identity transitions with literal identities.

Step 2 uses only the actual arrow normalization already in the item's statement and Step 1. Substitution at m=j cancels delta_(j,j,A) with its inverse; substitution of delta_(i,j,K) then gives the first requested equation. I checked its source and target, including that the target pair is (j,T_ij K). A comparison normalized only on same-field arrows would not suffice, so the report and proof explicitly retain the all-representatives hypothesis.

Step 3 uses no external theorem: it defines A, B, Q and writes a three-line calculation from naturality of q_j and the two assumed counit equations. A and B have source I_j T_X G_i L and target G_Omega I_j T_Y L. Q maps I_j T_Y F_i G_i L isomorphically to F_Omega I_j T_X G_i L. Both finite and common counit normalizations therefore apply at precisely their stipulated objects. The result is I_j T_Y(epsilon_i), without cancelling any inclusion functor.

Step 4 likewise uses only Step 2 and naturality. I checked the adjacent factors F_Omega(tau_X) F_Omega(tau_X inverse), counit naturality at the inverse Y transition, the common counit equation at i, and naturality of tau_Y at epsilon_i. The four-line chain displays these operations; it does not hide a separate identification or comparison lemma.

Step 5 cites def-weil-pbc-adjunction-mate for its transpose characterization and bijectivity. I read its actual statement, which supplies both assertions, and copied the exact transpose formula into citations.json. The two transformations are mates of the same inverse Q under F_i adjoint G_i and F_Omega adjoint G_Omega with side functors I_j T_X and I_j T_Y. Thus uniqueness applies without a hypothesis that any I_i is faithful. The given comparisons, not any newly chosen mates, satisfy the resulting equality.

I tested the identity case i=j with unitors retained, identity functors and identity comparisons, and zero objects/empty schemes. A nontrivial natural automorphism in a q_i is harmless because the hypothesis conjugates the whole common-stage arrow action and both q_i factors remain in Step 2. Omitting that arrow normalization would leave precisely this freedom uncontrolled; it has not been omitted. The calculation is abstract in the supplied categories, so it needs no geometric hypotheses beyond those required to supply them. All steps are under 2000 characters. B's self-contained-statement and source rules, C's completeness and citation rules, D's no-relabelling/no-circularity rules and E's hypothesis/endpoint/naturality checks require no further repair. The statement was not disputed or weakened.

## Unfinished work

None for this one-level split. The dry run and direct delivery are performed by the prescribed delivery tool; its independent maintainer review remains separate.
