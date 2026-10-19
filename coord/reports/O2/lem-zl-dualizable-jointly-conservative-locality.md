# N2 stage-1 delivery

## Files written

- `dag/nodes/sec-zeta-weil/lem-zl-dualizable-jointly-conservative-locality.json`: statement, split into eight proof steps; statement unchanged; no exact Mathlib match.
- `citations.json`: verbatim statement quotations for every proof-step dependency.
- `searches.jsonl`: actual search-command log; the item retains its four inherited searches and appends the six searches run here.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project `WeilConjectures/` for the exact blueprint tag and for jointly conservative/dualizable terminology. The source has no declaration of this general family-locality statement. Its `CategoryTheory.IsDualizable.map` in `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Rigid/OfEquivalence.lean:68` covers preservation only; the internal-Hom comparison criterion in `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:265,384` covers canonical comparisons and the dual construction, not the family-locality statement. These partial results are not attachments to the item.

## WANTED

None. The Hemo–Richarz–Scholbach paper and Stacks sources used here are present.

## Audit findings and corrections

The item was a statement-only child with no proof. Its statement is correct, including the empty-family convention, and was retained exactly. The proof is marked agent-written because HRS Lemma 4.5 supplies only the short formal inference for one conservative monoidal restriction functor, while this delivery expands the family version and both triangle calculations.

Read the item's inherited ancestor and its `blueprint_update`, the current main-20261015 ancestor proof, and its unit/chapter records. The current main ancestor is organized through finite-coefficient local constancy and relative duality; this child is the general tool needed by the inherited condensed-locality child, not a proposed replacement of any chapter or unit step. No unit record is changed.

An apparent reusable node, `lem-pc-dualizable-evaluation-criterion`, is restricted to D(O_X) on a scheme despite its generic title. It cannot be applied to the arbitrary categories of this item, so it is not cited. Likewise `lem-pc-dualizable-tensor-hom-equivalences` has scheme hypotheses. Instead the proof uses the existing fully general Mathlib leaves `lem-sfb-dual-tensor-adjunctions` and `det-sp-unique-right-adjoint`. The criterion's two triangle calculations are written in the item itself, not moved into a new node.

Mathlib hits `ExactPairing.ofFaithful` and `hasRightDualOfEquivalence` do not apply: the item assumes neither a faithful functor nor an equivalence nor already lifted duality maps. `MonoidalClosedFunctor` in Mathlib concerns cartesian closed functors. Read these candidates in the pinned Mathlib source. The second semantic phrasing found no exact match either. All six new search records exactly match the command log, and their hits were read. Blueprint-wide searches for dualizable, conservative, evaluation, dualizability criterion and tensor Hom, together with whole-DAG statement/title searches and Lean searches, found no generic duplicate beyond the existing tools reused here.

## Unfinished work

None in the one-level split. No Lean writing or compilation was performed. The existing dependency nodes are retained as the graph's independently reviewed tools.

## Not duplicates

No new nodes were created, so there are no new/existing duplicate pairs to justify.

## Review by N2

I read HRS, *Constructible sheaves on schemes*, Lemma 4.5 and its proof on printed page 10. Its lisse argument explicitly uses the restriction functor being monoidal, conservative, and commuting with inner Hom; the other constructible-stratification arguments of that lemma are not used. I read Stacks `categories.tex`, Tag 0FFL (strong monoidal coherence as recorded by the existing definition node), Tag 0FFP (`definition-dual`, including the following observation about functors), Tag 0FFQ (`lemma-left-dual`, including its actual forward/inverse Hom maps), and Tag 0FFR (`remark-left-dual-adjoint`). The warning in 0FFR matters: an arbitrary adjunction between tensor functors is not by itself enough to produce duality. Accordingly the proof constructs the canonical evaluation comparison and verifies both triangles, rather than assuming the warning away.

For step 1 I opened `def-sfb-strong-monoidal-functor` and `def-sfb-monoidal-category`. They state the exact tensorator naturality, associativity, and unit identities used in substituting the transported evaluation and coevaluation into the two triangles. Their hypotheses are arbitrary monoidal categories and a strong functor, supplied for each F_i. The displayed formulas include the inverse unit map for evaluation and the forward unit map for coevaluation, so both maps have the required source and target. This is the explicit construction of preservation, not a citation to the item itself.

For step 2 I checked that D=[K,1] belongs to C by the chosen internal-Hom assumption, and that evaluation is the inverse transpose of the identity of D. The comparison phi_M uses M tensor D, in that order, and its untransposed map has domain (M tensor D) tensor K. The cited monoidal-category node supplies its associator and right unitor. The inverse-transpose formula follows directly from naturality of the stated bijections, with no Yoneda or representability theorem being silently cited.

For step 3 I opened the full statements of `lem-sfb-dual-tensor-adjunctions` and `det-sp-unique-right-adjoint`. The first explicitly gives U_P left adjoint to U_D for a pairing with evaluation D tensor P and coevaluation P tensor D. Applying it to P=L and D=E gives the correct functors - tensor L and - tensor E. The step additionally writes the normalized forward/inverse Hom maps and explains their cancellation by the two triangles; thus its counit is the actual contraction 1_M tensor a, not an arbitrary unspecified adjunction. The second node states exactly that the internal-Hom transpose of that counit is a natural isomorphism. These two adjunctions share the same left functor, so its hypotheses are met in each D_i. Its counit compatibility is used to identify theta_M and q; the comparison phi^i_M is then identified by taking inverse transposes. This proves invertibility for every M in D_i, hence in particular for F_iM. Both tools are existing Mathlib leaves, so they are allowed without an off-unit route replacement.

For steps 4 and 5 I checked the unit map s:1_i to F_i1, u_i: F_i[K,1] to [F_iK,1_i], and the evaluation equality individually. Preservation of an arbitrary internal-Hom object alone would not suffice: these steps use the statement's explicit compatibility of adjunction transposes. Applying it to epsilon proves the evaluation identity; applying it to the untransposed definition of phi_M, with tensorator naturality and the unit/associator equations of the strong-functor node, gives the displayed canonical-map square. Step 5 spells out both inverse transposes, including s inverse. The strong-functor and monoidal-category citations actually state those equations and structures. I corrected the possible gap of comparing only isomorphic endpoints by specifying this equality of maps.

In step 6 only inverse composition and the assumed joint conservativity are used. No single F_i is assumed conservative, no selection of an index is made, and there is no product of categories or smallness assumption. For the empty set the conservativity hypothesis says that every arrow is invertible; the same proof applies. For an infinite set the argument remains pointwise in i, with no finite subfamily or compactness assumption.

Steps 7 and 8 use only the monoidal-category definition and the actual adjunction bijections from the statement. Untransposing phi_K c=j proves the K-triangle with the indicated associator and unitors. For the D-triangle, the step writes the two contractions of D tensor K tensor D tensor K and explains their equality by tensor bifunctoriality. After the K-triangle their composite is epsilon. Injectivity of transpose with domain D then gives g=1_D, since epsilon transposes to 1_D. Thus this last equality does not require a faithful F_i or detection of equality by conservative functors.

Small cases checked: the terminal monoidal category satisfies both conclusions; the identity family gives the ordinary dualizability criterion; an empty family forces every morphism invertible and therefore makes phi_K invertible; an infinite family creates no additional assumption. In vector spaces the canonical map fails for infinite-dimensional K, as expected, and the proof never infers dualizability merely from an isomorphism D=[K,1]. No new statement, definition, hypothesis, source error, or statement dispute was introduced. Every step is shorter than 2000 characters. The only non-elementary structural argument (step 3) cites both existing tools; the other steps are concrete substitutions, inverse compositions, and two short triangle calculations. The citation file contains an exact statement substring for each named dependency of each step.

Dry-run repair: the citation gate required at least 40 characters for the short displayed dual-tensor adjunction quote. Replaced all citation excerpts with the full verbatim statements, retaining exactly the same dependencies and proof.
