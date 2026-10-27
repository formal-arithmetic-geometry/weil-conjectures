# Stage-1 delivery: lem-sfb-naive-cotangent-localize-base

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-naive-cotangent-localize-base.json: item, statement unchanged, split into five proof steps. Mathlib searches did not find the entire canonical comparison with its chain inverse and derived conclusion. No new nodes and no new Mathlib leaves.
- citations.json: ten entries, one for every step/node citation, quoted verbatim from the current DAG statements.
- searches.jsonl: genuine msearch.py results for the item, with both natural-language phrasings and Loogle/grep/LeanSearch. The inherited Q87 search records are retained in the item; the Q58 records are appended.

## Attachments

None. Searches for the blueprint tag and for naive/cotangent/localization names throughout lean/WeilConjectures found no declaration of this item. PrincipalLocalizationNaiveCotangent.lean proves a different statement: principal localization of the target algebra, with an additional contractible summand. It does not attach this base-localization item.

## WANTED

None. All sources used are present locally.

## Corrections and discrepancies

The item had a statement but no proof. Its statement is correct and is retained verbatim. Tag 07BS leaves a direct computation implicit; the delivery supplies it for the specified standard presentations and proves that the canonical map is in fact a strict chain isomorphism. There is no need to appeal just to the existence of an unspecified homotopy equivalence between presentations.

The inherited blueprint ancestor is null (blueprint_refs.py ancestor prints None). Its existing detailed from.place and via trace are retained, and same_as is empty after blueprint searches for cotangent, localize and 07BS. The latest blueprint snapshot main-20261023-1620 and the recorded chapter/unit files were read. This is an algebraic prerequisite below the unit route and changes neither unit nor chapter. The unit is not the present item's statement, so no realization record is edited.

## Unfinished work

None for this one-level split. The proof uses existing DAG statements, all already Mathlib leaves, so no statement-only subproblem is needed.

## Not duplicates

No new nodes. The existing localization-flat, ideal-cotangent-flat-base-change-ring and polynomial-ring-kahler-basis-any-variables nodes were reused. The existing module-localization-exact, localization-module-over-localization and nl-presentations-homotopy-equivalent statements were also read; their theorems are unnecessary because the proof writes the elementary kernel and inverse formulas directly. In particular, no new node restates a clause of this item.

## Review by Q58

I read Stacks algebra.tex Tag 07BS (lemma-NL-localize-bottom), including its proof and the definitions/functoriality in section-netherlander (00S0). I also read algebra.tex Tag 00HT (lemma-flat-localization), Tag 00RX (lemma-differentials-polynomial-ring) and morphisms.tex Tag 0473 (lemma-conormal-functorial-flat), including its affine conormal calculation. There are no new-node sources to review. The proof follows the actual localized-presentation computation in 07BS, with its algebra spelled out, rather than routing through a different purity or SGA argument.

For step 1 I opened def-weil-pbc-module-localization and def-weil-pbc-mv-polynomial-ring: the former gives the fraction relation, zero criterion and inversion of denominators; the latter describes finite monomial expansions and polynomial evaluation. A finite product of coefficient denominators and a finite product of annihilators prove that the coefficient polynomial ring is the localization. No localization-injectivity theorem is being assumed. The map to B sends each denominator to a unit because the specified map from the localized base already exists.

For step 2 I again checked the localization definition. The formula epsilon_S(p/s)=s_B^{-1}epsilon(p) proves the exact kernel description immediately. The step uses neither flatness nor a general kernel-base-change assertion without a citation. The variables x_b ensure the two evaluation maps are surjective, including for infinite B.

For step 3 I opened lem-weil-pbc-localization-flat and lem-weil-pbc-ideal-cotangent-flat-base-change-ring. The former explicitly allows an arbitrary multiplicative set and requires just the unit, fraction and annihilator properties established in step 1; the latter states exactly the canonical isomorphism of conormal modules for a flat ring map and the image ideal J=IP_S established in step 2. I verified flatness is of P_S over P, not an unsupported flatness of B over A. I opened def-weil-pbc-module-tensor-product as well: its bilinear universal property supplies the multiplication map written in the step. The displayed balancing calculation and cancellation of an invertible denominator verify both inverse identities; no unquoted general tensor/localization comparison is used. All these cited statements are Mathlib leaves.

For step 4 I opened lem-weil-pbc-polynomial-ring-kahler-basis-any-variables. It explicitly covers arbitrary variable sets and, crucially, its last sentence supplies the base-changed B-module bases, not just a basis before tensoring. Both polynomial rings use the same variable set B. The canonical map fixes those basis vectors, which gives its inverse directly. The finite-variable polynomial-extension node would not suffice here and is not cited.

For step 5 I opened def-weil-pbc-kahler-differentials, the arbitrary-variable polynomial differential node and def-weil-abstract-derived-category. The first defines the universal derivation, the second explicitly states the partial-derivative formula, and the third defines the functor from complexes to the derived category. Comparing that formula after coefficient localization proves commutation with the actual differentials. Inverting a commuting square gives a strict chain inverse, hence zero homotopies; applying the derived-category functor preserves these inverse equations. No general uncited theorem about quasi-isomorphisms and homotopy equivalences is needed.

I checked B=0, S containing 0, S={1}, a coefficient localization killing a nonzero element, and infinitely many variables: no cancellation occurs in A or P, only of elements explicitly invertible in B or the localized tensor. If 0 belongs to S then B is the zero ring, so all B-modules in question vanish. No finite generation or nonzero-ring hypothesis enters. I reviewed delivery-errors B through E: all symbols and hypotheses are introduced; each non-elementary fact is a cited statement with a verbatim citations.json entry; there are no new nodes hiding a clause, no cycles introduced by the already-Mathlib dependencies, no proof step over 2000 characters, and no source or statement dispute. All writes are restricted to this sandbox; no Lean or compiler/build tool was used.
