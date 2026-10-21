# O3 stage-1 report: lem-weil-pbc-completed-scalar-unit-adjunction

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-completed-scalar-unit-adjunction.json`: statement, split into nine steps; no Mathlib match for the whole normalized comparison.
- `citations.json`: 28 verbatim statement excerpts, one for each step/node citation.
- This report. No new DAG nodes, Mathlib leaves, or unit-record changes.

## Attachments

None. I searched the whole project `lean/WeilConjectures/` for the exact blueprint tag and scalar/adjunction terminology, and the SixFunctors and CategoryTheory directories for completed adjunction and completion-unit terminology. The nearby `DerivedCategoryDerivedCompleteIntegral.completionAdjunction` in `CategoryTheory/DerivedCategory/Complete/IntegralCompletion.lean:158` is an integral constant-coefficient completion adjunction. `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_completionAdjunction_unit_app` in `SixFunctors/Adic/Reduction.lean:97` concerns reductions of that unit. Reading their signatures rules out either as an attachment: neither compares the two ambient coefficient categories, their strict towers, or the specified reconstruction and adjunction maps. No declaration stating this item's clauses was found; no compiler was run.

## WANTED

None. The local sources needed for the argument are available.

## Audit and changes

The item had an empty proof. Its statement, source, provenance, and coefficient hypotheses are retained. I supplied the actual constant/limit unit calculation, the quotient-augmentation equation, the pullback balancing calculation, and the comparison of completed Hom bijections. In particular the proof never treats restriction as fully faithful on ambient derived categories, and never assumes that ordinary inverse image preserves complete objects. Both shortcuts would leave a gap.

The blueprint ancestor is `lemma-weil-pbc-completed-exchange-coherence`. I read its current main-20261015 proof, especially its second paragraph about applying derived limit and conjugating by the same reconstruction maps. The ancestor does not itself prove the extra scalar-unit normalization; these steps are explicitly an agent argument supplying that normalization. I also read Stacks `proetale.tex`, labels `lemma-naive-completion` (099M) and `lemma-pushforward-Noetherian-case` (099N), including their proofs, and `algebraization.tex`, labels `lemma-derived-completion` (099B) and `lemma-derived-completion-koszul` (0A0E). The Stacks results supply the reflector and induced adjunction, while the existing strict-balancing and scalar-limit nodes supply the specific comparisons. I do not attribute the strict normalization equation verbatim to Stacks. No SGA source is used.

The chapter and unit records were read and left unchanged. This item is below the unit statement and does not replace a step of the proper-base-change route. `lem-sp-completed-pullback-adjunction` is declared as a tool use in `split_report`: it provides the generic constant-coefficient reflector and completed adjunction, rather than a different proof of proper base change.

The item's prior Mathlib records were read and retained, including their returned declaration lists. I additionally ran the logged searches in `searches.jsonl` with a different question: whether the flat scalar/derived-limit comparison preserves the constant/limit and quotient units. LeanFinder and LeanSearch returned ordinary algebraic completion, flat scalar extension, or quotient restriction results. Their types have no derived ring-sheaf tower or specified unit comparison. Loogle found `CategoryTheory.Adjunction.homEquiv_unit`, which is an elementary identity for an already supplied adjunction and does not state the item. The grep hits concern ordinary module restriction and algebraic adic completion. The earlier alternate phrasings likewise have no whole-item match. All four new records are copied from actual command logs; all services answered successfully.

## Not duplicates

No nodes were created. Whole-blueprint searches for `completion unit`, `scalar adjunction`, and `reconstruction`, and the whole-DAG inspection, found the existing completion, Koszul, direct-image, and strict-tower statements used here. The constant-completion equivalence already includes an unnormalized unit compatibility assertion, but not this item's identification with the specified lambda, rho, pullback reconstruction, and ordinary scalar adjunction comparisons. I reuse it only for its coefficient equivalence and flatness; Steps 2–4 verify the specified maps.

## Review by O3

I checked B–E against the node statements and the local sources, not just the dependency names. There are no new standalone statements to test or source, and none of the item's clauses has been moved to a replacement node. The nine steps carry the argument; their longest text is under 1,300 characters and none hides a longer unnamed comparison.

Step 1 uses the statement of `lem-weil-pbc-ringed-koszul-completion-reflector` for the Hom universal property and completeness of the Koszul limit, and `prop-weil-pbc-koszul-reconstruction` for the isomorphism respecting its unit and the quotient unit. These really give the quotient reflector even on incomplete inputs. `lem-sp-completed-pullback-adjunction` supplies the constant reflector, while `lem-weil-pbc-constant-completion-equivalence` supplies its equivalence with completed-ring complete objects and the flatness needed by `lem-weil-pbc-flat-ringed-diagram-restriction`. I verified the finite list of generators, small-site hypotheses, and the Noetherian finite/perfect quotient assumptions where used. The completed coefficient sheaf is never identified with the constant ring sheaf.

Step 2 uses the K-injective preservation assertion of the flat restriction node and the actual compatible-family normalization in `lem-weil-pbc-flat-scalar-tower-limit-square`. The definition of completed pullback states exactly how the constant/limit map is made by resolving a constant tower. Restricting that same tower resolution computes the other side, and both arrows have the same component maps into the ordinary limit. This is an equality of the specified maps, not an assertion that maps into a derived limit are detected by evaluated maps. Step 3 then uses the strict augmentation equation in `lem-weil-pbc-strict-quotient-scalar-balancing` and naturality of lambda to prove the displayed beta-unit equality. Both statements say these are actual strict-derived-diagram comparisons on arbitrary ambient objects.

For Step 4 I read the definition's strict quotient construction and its assertion that the resulting comparison is the completion unit. The pullback reconstruction is derived tensor reassociation before taking limit. The balancing node states the exact equation involving q and tau used to move that reconstruction across scalars. I retained the suppressed constant-coefficient reassociation in the text so that the domains agree. Lambda's naturality yields the displayed reconstruction equation, with no use of equality merely at each finite evaluation. Step 5 explicitly computes phi on the unit, then uses the constant reflector's injective Hom map for uniqueness. It uses the coefficient equivalence only on complete objects; ordinary pullback may be incomplete.

Step 6 uses `prop-weil-pbc-direct-image-limits` exactly for preservation of completeness, `def-weil-pbc-proetale-operations` for the ordinary unbounded adjunction, and the completion Hom bijections for the first part of the completed adjunction. The flat restriction node's statement explicitly says the adjunct of the scalar-restricted map is chi times the restriction of the original adjunct. Substituting the proved unit equation gives that very formula for t composed with j. Thus both completed Hom bijections, rather than just abstractly isomorphic left adjoints, agree. Step 7 evaluates those bijections on identities for the units and counits. The direct-image composition comparison is checked by its ordinary adjunct, using the underlying inverse-image comparison and the identity/composition coherence of `lem-weil-pbc-profinite-coefficient-inverse-image`. The bijection in `def-weil-pbc-adjunction-conjugate` then identifies the completed composition and identity maps. This is formal injectivity of the stated bijections, not a new coherence theorem assumed without citation.

Step 8 uses the naturality assertions for q, rho, and lambda in their existing statements. The report's node writes the actual postcomposition by the derived limit of the reduction of an isomorphism h, and the resulting equality with the naturality square for the fixed reconstruction. Step 9 only substitutes a complete direct image, justified by the preservation clause quoted from `prop-weil-pbc-direct-image-limits`. This checks the final applicability clause without introducing properness or a boundedness or constructibility restriction.

I tested the formulas on zero inputs, the identity edge, nilpotent I, I=0 when permitted by the finite quotient datum, and I=A. Zero inputs give zero maps; for the identity edge the comparison is the unit-normalized comparison of the two reflectors. Nilpotent I reduces the completion to the eventual constant quotient, with the same x-to-x-tensor-1 augmentation. For I=A the completed coefficient ring and both full complete categories are zero, and all equations and uniqueness statements hold. The construction and Hom arguments apply to unbounded inputs and do not invoke convergence of a spectral sequence. I found no statement dispute requiring correction.

## Unfinished work

None in this stage-1 split. The cited unsplit strict-balancing and scalar-limit nodes remain separate existing items; this delivery supplies no Lean proofs and makes no claim that those dependencies are already formalized.

## Validation

The citations writer checked every one of the 28 excerpts as a literal substring of the cited node's statement. The required server dry run and push are recorded below after execution.

The first dry run requested longer excerpts for the ordinary-adjunction citations in Steps 6 and 7. I replaced those excerpts with the full relevant signature/adjunction passage and reran the command. The final dry run exited 0 with `OK (not pushed) deliver/O3/lem-weil-pbc-completed-scalar-unit-adjunction at 901338cd40b: preflight passed`, including the required server DAG and split checks. Delivery follows this successful completed dry run.
