# Worker report

1. Files written:
   - `dag/nodes/sec-smooth-purity/lem-pur-intrinsic-associator-shift-square.json`: statement unchanged; five proof steps; status split.
   - `dag/nodes/sec-smooth-purity/lem-pur-intrinsic-scalar-normalization-formulas.json`: new statement-only lemma; unsplit, no Mathlib match. It records the actual integral associator component, ordinary-to-completed shift normalization, and rational associator component, together with the ordinary exact tensor presentation. It does not assert an associator shift square.
   - `citations.json`: one verbatim statement quotation for every step/node citation.
2. Attachments: none. Searches for the item tag and intrinsic scalar-associator shift theorem in `lean/WeilConjectures/` found no declaration giving this item. `rationalConstructibleScalarComp_commShift` in `lean/Sheaf/Paper/ScalarExtensionAssociatorShifts.lean` is the older coefficient presentation and is not an attachment of this item.
3. WANTED: none.
4. The statement has no discovered error. The imported node had no proof. The potential error was using the old associator shift theorem as if its categories were definitionally the intrinsic ones. This delivery avoids that identification entirely. The blueprint explains exact derived scalar composition but does not write the intrinsic normalized shift square; the proof is therefore marked agent-written.
5. The item is finished at stage 1. The new normalization lemma is deliberately not split here. Its future proof can use the named normalization specifications already present in the source; this report does not claim that a sorry declaration proves anything.

## Earlier evidence and searches

The required archive glob over all groups returned no matching abandoned attempt. The initial sandbox contained only dispatcher marker files, no item, report or searches. I copied the live item into the sandbox and kept its original statement, source, blueprint ancestry, creation record and five Mathlib search records. Those five records are attributed to the original NR-created item, not to searches I ran. My additional searches are in `searches.jsonl`; the item and new node record only queries actually run through msearch.py. Each has LeanFinder, Loogle, grep and LeanSearch evidence and a second semantic phrasing. No unavailable service was called a no-match.

The semantic hits include ordinary tensor associators, monoidal localization, ordinary adic completion, and generic CommShift comparisons. None states the specified intrinsic completed construction's component normalizations. For the item, NatTrans.CommShift.associator is the reassociation of *functor composition*, not the natural tensor compositor between different scalar functors. Loogle also finds a newer Mathlib exact-derived-composition API; the pinned local `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean` has only the 149-line exact-functor/factorization API, and the logged grep finds no mapDerivedCategoryCompIso or mapDerivedCategoryNatIso. I read that file and did not declare a leaf from the online index alone. The existing exact-factorization and localization-universal-property nodes suffice to prove ordinary shift compatibility directly.

## Sources read

For the item I read the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-sfb-filtered-two-colimit/det-def-sfb-filtered-two-colimit-model.proof.md`, especially its common-stage transport and comparison-functor equations, and the exact-derived scalar-composition proof `.../sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md`. The chapter and unit records were read; no chapter, unit statement, or unit route is changed.

For the new normalization node I read `SfScalarExtensionComposition.lean:810-850` (the integral component specified by conjugation), `:970-1020` (the raw rational component as the localization image), `GeneralAlgebraicallyClosedCoefficientStages.lean:266-300` (the actual integral ordinary-to-completed shift equation), `:538-586` (the specified scalar associator and composite-inclusion equality), and the transition/shift definitions and uniqueness specifications at `:236-266, 398-437`. I also read the ordinary associator definition in `ScalarExtensionComposition.lean:667-679` and the ordinary tensor construction and exactness statement in `IntegralScalarExtension.lean:135-180, 270-282`. These concern the intrinsic categories on an arbitrary scheme; the characteristic parameter is zero and only used in preservation proof fields.

The direct ordinary shift calculation uses the statement of `lem-weil-pbc-exact-functor-derived-factorization`, not a result about existence of exact functors alone. The localization equality test is clause (3) of `lem-weil-pbc-localization-universal-property`. These existing nodes supply the general descent facts; the generator calculation and signs are written in step 2. No SGA source is used.

## Not duplicates

lem-pur-intrinsic-scalar-normalization-formulas vs lem-general-algebraically-closed-coefficient-stages: the existing stage-system statement gives normalized shifts, exactness, parameter independence and associator cocycle, but not the three component equations relating its precise associator and shifts to ordinary extension and raw localization.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-weil-scalar-extension-composition: existence and naturality of the rational scalar composition isomorphism do not state its integral-conjugation or localization-image characterization or the prescribed integral shift equation.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-weil-scalar-associator-shifts: the older theorem asserts shift compatibility on a different finite-field-datum coefficient presentation. The new lemma specifies the intrinsic components and asserts no associator shift square.

lem-pur-intrinsic-scalar-normalization-formulas vs def-zl-normalized-integral-scalar-comparison: that definition specifies chi on good complexes; it does not identify the integral/rational associator components or give the ordinary-normalized integral shift equation.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-route-integral-transition-comm-shift-exists-unique: the existing theorem specifies the integral shift for a finite-field datum. It states neither the p=0 associator conjugation formula nor its rational image.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-route-transition-comm-shift-exists-unique: the existing theorem uniquely specifies the rational shift from degree one, without giving either associator component formula.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-weil-finite-free-completed-scalar-comparison: that theorem supplies the finite-free coefficient extension and completion comparison, not the intrinsic integral/rational associators or their shift normalizations.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-pur-integral-coefficient-model-comparison: that theorem concerns purity adjoints for a smooth separated map between finite-type schemes over a fixed finite-field closure. It cannot supply these formulas on arbitrary Y with no datum, and does not specify the normalized integral scalar shifts here.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-zl-point-heart-scalar-normalizations: the point-heart theorem concerns degree-zero section/extension comparisons on a point with a fixed datum, not intrinsic integral objects on arbitrary Y.

lem-pur-intrinsic-scalar-normalization-formulas vs lem-weil-integral-twist-ambient-coherence: the existing result concerns Tate twists with an invertibility hypothesis and explicitly excludes the restricted sfIntegralScalarComp; the new lemma is about the actual restricted and rational associator components and integral integer shifts.

## Review by NC

I checked B--E against the item, the new node and the sources, rather than just running the scripts. The new statement introduces its rings, ambient module derived categories, full integral inclusions, ordinary and completed transitions, localization maps, and all comparison maps. Its only deferred content is the characterization of existing constructions. It contains no proof sketch, proof step, or proof dependency. It is not a renamed version of the desired square: the square is derived in steps 2--5. Blueprint searches for the intrinsic normalization and associator/shift concepts found no blueprint node stating this interface. The broader DAG searches found the adjacent nodes compared above.

Step 1 takes exactly the new node's three formulas and ordinary exact presentation. Step 2 uses its ordinary balanced tensor map, the exact-factorization node's statement that the factorization commutes with each shift, and the universal-property node's statement that equality on localized complexes implies equality of natural transformations. In degree r the tensor-generator map is unchanged on replacing P by P[n], and both differentials acquire the same (-1)^n. This checks negative n as well as positive n, without a boundedness assumption or a K-flatness claim for arbitrary inputs.

Step 3 uses the new node's ordinary-to-completed normalization equation, so chi is a shift-compatible comparison for precisely the chosen integral shifts. Its inverse compatibility follows by multiplying the equation by inverse components. The existing Mathlib composition/whiskering node explicitly states the composite comparison and each closure operation; applying it to the fixed autoequivalence [n] gives the composite square. Cancellation of the final inclusion comparison followed by faithfulness of the full inclusion gives equality of integral maps. This uses no inference from equality of reductions.

Step 4 uses the raw tensor-Hom formula and induced shift of the rationalization definition, the explicit degree-one identity comparison of the scalar-localization definition, the exact localization comparison of the triangulation lemma, and the stage lemma's uniqueness of the full normalized coherent integer-shift structure. I wrote the candidate with both q and q inverse rather than assuming the localization comparison is a literal identity in every degree. Pure-tensor naturality, inverse cancellation, and the zero/add equations are spelled out. This constructs the full coherent family and invokes normalization uniqueness only after checking it has the required degree-one component.

Step 5 uses the new node's rational associator component and the rationalization definition's scalar action on integral arrows. Precomposition by (T_LM T_EL)(q_E) has the correct source and is invertible. On the left, naturality of a cancels the source q_E with its inverse in the normalized shift. On the right the intermediate q_L and inverse cancel, and naturality of q_M across b_K gives the displayed two Q_M-images. Those images are equal by step 3. This is the actual comparison calculation, not an unspecified transport assertion.

I checked E=L, L=M and E=L=M: the formulas retain the tensor associator and multiplication/completion units and never assume the reflexive transition is literally the identity. The zero object and zero maps satisfy the same equations. Hom localization need not be faithful: the argument only applies its functor to an already proved integral equality. No Noetherian, dimension, ell-invertibility or finite-field base hypothesis was introduced. Small coefficient models and coefficient-map equality casts are those specified in the new node, so independent universes do not become an equality assumption. All proof steps are under 2000 characters; no long-step lemma was hidden. Every cited quotation in citations.json was checked as an exact substring of its node's statement. All off-unit proof tools used by the item are existing Mathlib leaves, so no undeclared route departure is needed. No repository, launcher, Lean file or compiler was written or run.

## Validation

The required server dry run and final push are recorded below after execution.

First dry run stopped at the citation gate because two quotations were shorter than 40 characters. Expanded them to the cited statements; no mathematical claim was changed.

Required server dry run passed: `OK (not pushed) deliver/NC/lem-pur-intrinsic-associator-shift-square at 73bd330218f: preflight passed`. The process exited 0 before starting the final push. Five proof-step lengths are 566, 1070, 916, 1317 and 1233 characters. One new node, zero new Mathlib leaves.
