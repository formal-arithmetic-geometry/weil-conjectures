# Q35: lem-pod-hom-chain-pairing-naturality

## Files written

- `dag/nodes/sec-six-functors/lem-pod-hom-chain-pairing-naturality.json`: existing statement, now split into six proof steps. Not a Mathlib leaf: the search hits give generic individual naturality laws, not this conjunction for the specified ordinary/exceptional pairing.
- `citations.json`: six verbatim statement excerpts for all step/node citations.
- `report.md`: this report.
- `write_split.py`: sandbox-only preparation script; not part of the DAG delivery.

No new nodes; no new Mathlib leaves. The inherited statement, source, creation and blueprint provenance are retained. The inherited six Mathlib searches are retained, with four actually executed searches appended from this sandbox's log.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, chain/pairing terminology, and the six-functor counit/projection declarations found no project declaration giving all six identities for these specified maps. Partial generic lemmas are not attachments.

## WANTED

None. All sources needed for this calculation are available locally.

## Errors and changes

The item had no proof. Its creating node separates finite-Tor domains, counit identification and target naturality into distinct items. I preserved that division: the finite-Tor memberships come from the existing sibling `lem-pod-hom-chain-ctf-domains`, and the present item proves target naturality directly. I did not cite the creating `lem-pod-hom-chain-counit-formula`, which already depends on this item.

No statement dispute or source correction is needed. The statement supplies the exceptional adjunction as data; the argument does not infer an unconditional ambient exceptional adjoint. Naturality only needs the adjunctions on their stated domains. Evaluation is the chosen left-factor counit, so no symmetry/sign comparison is hidden.

## Unfinished work

None for the stage-1 split. Existing dependencies may remain unsplit; no claim is made here to prove their statements. No Lean was written or compiled.

## Not duplicates

No new nodes. Whole-DAG searches for counit naturality, evaluation naturality, the relevant Mathlib declarations and adjunction statements found the reusable `lem-weil-pbc-adjunction-of-natural-bijection`. Blueprint searches for `counit`, `evaluation`, `counit naturality`, `closed monoidal`, `projection pairing` and `tensor–adjunction` found the broader tensor-adjunction theorem, not another blueprint statement of the six specified identities. The item's nearest blueprint ancestor remains `thm-pod-identification-of-the-comparison`, with its existing via list. Thus `same_as` is empty.

## Review by Q35

I read the six-functors chapter record and the package unit, including the fixed route and its adjunction, projection and duality clauses. For the item I read main-20261015's `fix-lem-tensor-adjunction.proof.md`, especially Step 1 and its concluding naturality assertion, and `thm-pod-identification-of-the-comparison.proof.md`, especially the paragraph describing pullback, ordinary counit, evaluation, pushforward and exceptional counit. The blueprint leaves these naturality squares implicit. I expanded them, with proof origin recorded as agent rather than claiming the detailed calculation was present verbatim.

I also read Stacks `categories.tex`, Tag 0037 (`definition-adjoint` and its following paragraph): the Hom bijections are functorial and their adjunction maps form natural transformations. This is exactly the general-purpose fact in the existing Mathlib leaf `lem-weil-pbc-adjunction-of-natural-bijection`. I read that node's full statement, including its unit/counit formulas and naturality assertion. The Mathlib search hits for `Adjunction.counit_naturality` and `ihom.ev_naturality` support using this existing leaf, rather than manufacturing separate nodes for elementary instances. I read Mathlib's `CategoryTheory/Monoidal/Closed/Basic.lean`, lines 92–111 and 165–175: evaluation is the counit and its naturality is the naturality field of that transformation. No new node requires a separate source review.

For step 1 I read the full statement of `lem-pod-hom-chain-ctf-domains`. It states precisely the membership of C, A_N, B_N, the exceptional image and internal Hom, and the pullback/tensor objects for every finite-Tor T. I applied it twice, with N and N', and then with T=A_N and A_N'. All its geometric, coefficient, adjunction and finite-Tor hypotheses are those already supplied by the item. This avoids silently assuming the projection map can be used with an unverified A_N.

For step 2 I read `fix-prop-adjunctions`, clauses 1 and 2, which supply the ordinary and the assumed exceptional adjunction on the relevant full subcategories. Clause 2's conditional exceptional hypothesis is respected by the item's explicit supplied-adjunction assumption. The existing general adjunction leaf says that each counit is a natural transformation. I wrote its component equation and substituted h for the ordinary adjunction and r for the exceptional one; a is defined as Rf_*h. Thus no cited definition is being used as an uncited preservation or existence theorem.

For step 3 I read `lem-pod-closed-uncurry-laws`. Its statement identifies evaluation with the counit of the left-factor adjunction A tensor - left adjoint to [A,-]. Applying the same general adjunction leaf at Rf^!r gives exactly the displayed evaluation square, since h is that right-adjoint image. This does not require extracting naturality from the proof of the closed-uncurry node, nor changing between right- and left-factor adjunctions. The restricted adjunction remains the one specified in the item's hypotheses.

Step 4 contains the explicit tensor-functor calculation for q, using only steps 2 and 3, associativity and preservation of composition by tensoring with M. There is no new lemma or uncited non-elementary input in this substitution.

For step 5 I read `fix-prop-projection-formula` and checked its phrase “natural in K and L” against the step's use. K=M is bounded constructible and both choices L=A_N,A_N' have finite Tor amplitude by step 1; f is separated finite type. The transformation is the specified map, as in the item and `def-exchange-projection`, whose full definition I also read. The equation used is the forward projection naturality square; no inversion or independent choice of projection isomorphisms occurs. This is a theorem citation, marked non-elementary.

Step 6 writes out the final p equation using step 5, functoriality of Rf_!, step 4 and the exceptional equation of step 2. Every intermediate composite has the same source C tensor A_N and target N'. It uses no further comparison theorem. Because all maps were already supplied at the chosen coefficient stage, integral completion and field coefficient transport require no new descent or conservativity argument here. In particular I did not try to reduce rational coefficients to finite torsion coefficients.

I checked B through E of delivery-errors, including both copies in the file. There are no new-node form, duplication or clause-relabeling issues. All cited statements were opened; `citations.json` contains literal substrings checked while writing. Every theorem input is either cited or a previously proved step; the elementary steps are only natural-transformation component equations and explicit functorial substitutions. The only non-Mathlib off-unit proof citation is the already specified generic evaluation convention `lem-pod-closed-uncurry-laws`, declared in `split_report.tool_uses`; this does not alter the package route. The ordinary/exceptional adjunction node is on the unit's mate route.

As edge checks, for r an identity, all three counit/evaluation squares and both composite formulas reduce to identity/functor laws. For f an identity with the identity adjunction data, q and p reduce to the ordinary evaluation square. If M=0, or the source/target object is zero, the equations reduce to equality of the corresponding zero composites in these additive categories. No step assumes r is invertible, N is nonzero, f is proper, or a coefficient is a field. All steps are shorter than 2000 characters; none hides a separate comparison or induction.
