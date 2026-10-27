# Worker report — Q139

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-ordered-finite-model-filtration.json`: statement item split into seven steps, unchanged statement, no new nodes and no new Mathlib leaves.
- `citations.json`: a verbatim statement quote for every node used in each numbered proof step.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is sandbox-only preparation material.

The existing item was unsplit and the sandbox initially contained only dispatcher markers. There was no previous proof/report to retain. The new proof reuses the existing DAG instead of creating common-refinement, finite-field support or nilpotent-invariance duplicates.

## Attachments

None. The blueprint tag and concept searches in `lean/WeilConjectures/` found no declaration proving the item. Existing declarations of generic refinements or inverse images do not state its finite-model and prescribed-isomorphism clauses. Source declarations containing sorry were not treated as completed proofs. No compiler, Lake, or Lean-writing command was run.

## WANTED

WANTED: an exact reference for the original all-norm-continuous coefficient topology comparison in blueprint direct-images paragraph (3), as already recorded by the item's source. This split proves a conditional assembly statement from the finite field models explicitly supplied in its hypotheses. It does not assert a finite-model existence theorem or the comparison of C and B. All non-elementary assembly inputs are existing DAG statements, and no missing norm-topology reference is used as a black box.

## Corrections and source scope

No statement was changed. The finite-field models are hypotheses, so this item does not need to construct them or choose one common field. The old statement dependency on derived extension of scalars was replaced by ordinary change of scalars; the displayed model tensors and psi are ordinary tensors. The fibre-product and finite-stratification definition dependencies were added.

The inherited blueprint ancestry is broken: `blueprint_refs.py ancestor` prints `None`. The item and its ancestors already carry `from.node: null`. I retained that truthful value and the inherited via chain, with a concrete place in main-20261015 direct-images proof paragraph (3); I did not invent a blueprint ancestor. Whole-blueprint searches for stratification, filtration and finite models locate the existing common-stratification and filtration family but no equivalent imported statement. The item's `same_as` stays empty.

The main blueprint paragraph (3) does not prove the norm coefficient comparison. The proof is marked agent-origin and uses the existing field-independent support tools below that paragraph. The unit and chapter records are unchanged. Off-unit tools are declared in `split_report.tool_uses` with their roles.

## Not duplicates

No new nodes were created. In particular I reuse `new-det-lem-coefficient-heart-common-stratification-refinement`, `new-det-lem-coefficient-heart-common-stratification-lisse`, `lem-sfb-coefficient-heart-lisse-extension-constructible`, `new-lem-weil-pbc-condensed-surjective-closed-equivalence`, `lem-weil-pbc-proetale-ringed-open-closed`, and `lem-sfb-locally-closed-module-extension-coherence`. The finite-constant-model and normalized-continuous-qbar filtration nodes were read too; neither states compatibility with the specified finite models, so neither was misidentified as this item or used to assume the conclusion.

## Review by Q139

I read the stage-1 brief, stage document, worker role, GOAL, SETUP's three-level route, the item's chapter and unit, and delivery-errors sections B–E including the merged copy. I read main-20261015 `sk-thm-sf-ctf-stability-direct-images.proof.md` paragraph (3), `sk-lem-coefficient-heart-common-stratification.proof.md` clauses (1)–(3), and `sk-cor-coefficient-heart-ii-generation.proof.md` converse/single-sheaf paragraphs. The additional primary passages read were Stacks topology.tex Tag 09Y5 (`lemma-noetherian-partition-refined-by-stratification`), proetale.tex Tags 09AA (`lemma-closed-immersion`), 09AB (`lemma-thickening`), 09BN (`lemma-open-immersion`), 09AH (`lemma-ses-associated-to-open`), and derived.tex Tag 0152 (`lemma-derived-canonical-delta-functor`). The proof uses the module lifts as explicitly stated by the cited nodes; it does not pretend those lifts are literal statements of the set-topos passages. No SGA source was used. No new node needs a separate source review.

Step 1 uses the finite-type-over-Noetherian statement to make X Noetherian, finite-field lisse-extension constructibility for each F_a, normalized immersion coherence to match the supplied factorization, and the constructible definition to choose P_a. The field k is Noetherian and each E_a is a finite intermediate field, exactly the hypotheses of these tools. The support theorem's degree-zero constructibility implies sheaf constructibility by H^0. I checked that its coefficient is the condensed finite topological field E_a, not a discrete field or the finite-subextension algebraic closure.

Step 2 uses the actual image-only common-refinement theorem, whose conclusion includes the open prefixes and which allows an empty input family or empty X. Its coefficient parameter is unused, so varying the E_a does not obstruct the simultaneous geometric refinement. The lisse theorem's clause (2), read verbatim, applies separately for every finite-field F_a and every P_a; it asserts lisse on every image refinement without a factoring morphism. The resulting stratification is adapted to all F_a, not only the selected one.

Step 3 uses base-change stability of immersions, then the closed-image criterion, then the arbitrary-condensed surjective-closed equivalence. I checked that the latter's displayed Lean statement quantifies over every commutative condensed ring, so it applies to B=C(-,Omega) with all continuous maps; the finite-ring-only invariance node would be insufficient. Surjectivity of q follows at each point from image containment and the residue field of an immersion. A surjective immersion has closed image even when its defining ideal is not zero. This explicitly avoids delivery-error E3: no scheme factorization is inferred from set containment.

Step 4 uses normalized a^*a_! = id from module immersion coherence and the actual inverse-image composition theorem. For tensors it uses the strong monoidal comparison theorem, the inverse-image left-adjoint property, the relative-tensor coequalizer definition, and the monoidal coefficient pullback composition. These say precisely the maps being compared, rather than just defining a vaguely related notion. The map on W is the pullback of the given phi_a under those identifications; full faithfulness of q^* supplies a unique map downstairs, and reflection of isomorphisms makes it an isomorphism. Its pullback equality holds by construction, so no unproved assertion that arbitrary comparison diagrams commute is hidden. There is no flatness assumption or derived scalar calculation in this step.

Step 5 uses arbitrary-ring module localization, the Noetherian subscheme/open quasi-compactness clause of the locally closed extension theorem, the reduced-closed-subscheme existence theorem for the complementary closed subsets, and the closed-image criterion for R_t in V_t. All localization complements are quasi-compact opens in Noetherian schemes. I added the reduced-complement existence citation during self-review instead of using that geometric construction without a node.

Step 6 applies exact open extension to that sequence and uses normalized immersion composition to identify its first and last terms, including the two orders of factorization. The nested counit equality is justified by adjunction: both maps transpose to the identity on the smaller open, which fixes the actual inclusion into M. The quotient is therefore the quotient of the specified subobjects; psi_t^{-1} gives the finite-model identification. Step 7 uses the general derived SES triangle node, which states the required triangle of degree-zero objects in the ordinary derived category of any abelian category. No bounded derived category or finite-coefficient recollement is substituted.

Small cases checked: X empty; M zero on nonempty X; ranks zero; one stratum; disconnected X; different fields on different strata; repeated open prefixes and zero successive quotients. For the image-only issue take X=Spec(k[epsilon]/epsilon^2), S=X_red and M free: an R with a nonreduced structure need not factor through S, but R times_X S -> R remains a surjective closed immersion and the descent works. The argument nowhere replaces that immersion by a scheme isomorphism. It also permits arbitrary given phi_a, since psi_t is descended from that particular map rather than chosen independently.

I checked C1 and C4 against the complete statements of every cited node and wrote verbatim quotations in citations.json; B is satisfied without new statement-only nodes, D is satisfied by an actual refinement/descent/localization argument instead of clause restatements, and E is checked by the hypotheses and examples above. All seven steps are shorter than 2000 characters. A read-only dependency traversal found no path from the cited nodes back to this item. The fresh Mathlib search log has two different LeanFinder phrasings, Loogle, grep, and LeanSearch; the results concern coborder lifts, ideal/module filtrations, local cohomology and sheaf colimits, and none proves the item.

## Unfinished work

None in this one-level split. The cited existing unsplit statements retain their own independent obligations. Server dry-run and push results are recorded by the delivery command.
