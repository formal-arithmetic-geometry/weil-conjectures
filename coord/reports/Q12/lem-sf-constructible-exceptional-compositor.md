# Stage-1 report: lem-sf-constructible-exceptional-compositor

## Files written

- dag/nodes/sec-six-functors/lem-sf-constructible-exceptional-compositor.json: statement, split into seven proof steps. Not a Mathlib leaf: Mathlib supplies the categorical conjugation infrastructure, not the actual constructible geometric functors at all four coefficient stages.
- citations.json: twenty verbatim statement excerpts, one for each step/node citation.
- No new DAG nodes; no new Mathlib leaves. No Lean files, compiles, builds, repository writes or chapter/unit changes.

## Attachments

None. The project search found `AlgebraicGeometry.ProEtale.exists_rightDerivedUpperShriekAdjunction_comp_eq_of_finiteTor` in lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/UpperShriekComposition.lean:309. It gives a finite-stage restriction with explicit preservation hypotheses, not the all-stage theorem and its specified canonical Hom action, compactification independence and shifts. The ambient variants impose an ambient exceptional-adjoint datum, which this item does not assume. Therefore neither is an attachment for this item. The item's blueprint tag has no declaration in WeilConjectures.

## WANTED

None. The argument uses the local blueprint, local Stacks sources and the existing DAG interfaces. Its categorical expansion is marked agent-written rather than attributed verbatim to Stacks.

## Corrections and source audit

The statement is retained verbatim. No STATEMENT-DISPUTED issue was found. The imported `same_as` entry `pur9-def-upper-shriek-composition` was removed after reading it: it defines an inverse-direction finite-stage comparison on bounded constructible objects, and does not state the all-stage finite-Tor isomorphism/counit/shift theorem. It is related, but not the same statement. No imported blueprint or flag field was deleted.

Read the chapter and unit, the current main-20261015 Verdier-exchange proof Step 1, and its final naturality/compatibility sentence. This split realizes that mate argument and stays below the same unit; it does not use biduality or an ambient pro-etale exceptional adjoint. For the geometric left compositor read Stacks more-etale.tex Tag 0F7J (`lemma-shriek-composition`), including its proper/open four-line construction and common-refinement argument. For the composite adjunction read categories.tex Tag 0DV0 (`lemma-compose-counits`) and Mathlib Adjunction/Basic.lean:567-590. For conjugation read Adjunction/Mates.lean:275-288 and 425-438; the chosen direction is the conjugate of alpha inverse, not alpha. Read the existing coefficient adjunction and compactified-tower node statements in full, and their named realization and shift interfaces before citing them.

Mathlib queries and their actual hits are in searches.jsonl and appended to the item's existing search history. Loogle found conjugateIsoEquiv, which is already represented by def-weil-pbc-adjunction-conjugate; LeanFinder/LeanSearch found ordinary sheaf, spectrum or generic category-theory results. The grep found no exceptional-composition implementation in Mathlib. A second semantic phrasing also gave ordinary sheaf infrastructure. These do not identify the actual all-stage operations and do not make this item a one-line Mathlib specialization. No queries were invented, and earlier search records were preserved.

## Review by Q12

I checked delivery-errors B through E against each written step and the actual statements cited. There are no new nodes to be self-contained, searched or tested, and no unsplit new lemma concealing the item's conclusion. Existing derived isomorphisms are used in the derived category throughout. The maximum proof-step length is 1218 characters; no step exceeds 2000 characters.

Step 1 cites the coefficient adjunction theorem specifically for actual functors, exactness, finite-Tor preservation, and refinement-compatible counits. The finite compact-support composition theorem supplies the canonical alpha on bounded-below etale-origin inputs, and the compactified-tower theorem explicitly supplies its completed and field counterparts and the refinement cocycle. This is not a claim that finite Stacks 0F7J alone treats integral coefficients. The objects here are separated finite type over the fixed algebraic closure with ell invertible, exactly within both interfaces. Restriction from the bounded constructible category to the full finite-Tor category uses preservation by those actual functors, not a new choice of functors.

Step 2 uses the composite-adjunction statement for both the composite Hom equivalence and the pasted counit. The conjugate node explicitly states the direction of the correspondence and preservation of inverse isomorphisms. With first left adjoint A=F_g F_f and second F_x, tau must be alpha inverse. I checked its component has source G_f G_g L and target G_x L. The formula ends with G_x of the pasted counit. Thus the proof does not hide a new categorical existence lemma.

Step 3 uses the transpose clause of the actual mate statement and the composite counit formula, not a mere full-faithfulness or definition of adjointness without the needed clause. After cancelling alpha, injectivity of the single adjunction Hom bijection gives uniqueness of each component. Step 4 then writes the calculation for an arbitrary map u, explicitly uses naturality of alpha inverse to rewrite its precomposition, and obtains exactly h mapped to h composed with alpha inverse. Both are elementary manipulations of the cited formulas; no unrecorded Yoneda theorem is needed.

Step 5 uses precisely the statements that refinements identify alpha and preserve the adjunction counits. Under those coordinates both candidate c components have the same F_x transpose. The injectivity already proved gives equality. This spells out what transport and compactification independence mean and checks the refinement cocycle, without claiming literal equality of different compactification functors.

Step 6 uses clause (3) of the finite structural-map shift node for the canonical compact-support compositor. The integral realization-shift statement includes direct-image compositors, proper/open interchange and every integer shift, for actual derived-system maps; this is what is needed to identify the specified integral alpha. Its domain is normalized systems with compatible etale-origin witnesses and uniform finite intervals. The inputs and intermediate values form a finite list of constructible finite-Tor objects of the actual operations from step 1, so their reductions have common finite intervals by the integral category conventions. The rational-transport statement supplies exact localization and transformation extension; the coherent-pair descent statement preserves composition and equations for compatible coefficient families. The compactified-tower statement supplies those existing comparisons. Thus no arbitrary family of finite arrows is lifted, and finite evaluation is never assumed faithful.

Step 7 checks shifts using the explicit conjugate formula from step 2. The adjunction shift lemma gives the canonical right-adjoint shift and unit/counit compatibility for the specified left shift; the operations carry these canonical exact-adjunction shifts. The composition/whiskering statement provides the composite shifts and closure of compatible transformations. Applying it to the three displayed factors of c proves its shift equation. The same rule gives the composite counit shift. Its generic statement uses [1]; the operations here have coherent integer shifts, and iteration, inverse shift and the coherence isomorphisms give the integer version. This is a direct categorical application, not another geometric lemma.

I tested identity f and identity g (identity alpha gives the usual identification of the right adjoints); empty schemes and zero objects (all formulas have their unique zero components); n=1; and a structure map to the point (the mate gives exactly the dualizing-object comparison required by the unit). The direction of c and of the precomposition alpha inverse agrees in each case. Finite extensions use the same construction with E replaced by E'; this item does not assert a coefficient-compatibility equation and does not use the sibling finite/adic coefficient-compositor obligations circularly.

## Not duplicates

No new node pairs. Whole-DAG and blueprint searches for composition, compact-support composition, conjugate and shift compatibility found the existing generic tools used here. In particular no new clause of this item or duplicate categorical lemma was created.

## Off-unit tools

The split_report.tool_uses entries explain the all-stage left compactified-tower comparison, finite structural shift, integral realization-shift, rational transport and common-stage descent. These are prerequisites used as generic tools, not replacements for the unit's mate-of-composition route. Existing categorical Mathlib leaves require no extra route authorization.

## Unfinished work

None within the authorized one-level split. Existing cited prerequisites retain their own proof obligations; no attempt was made to split or modify another item.
