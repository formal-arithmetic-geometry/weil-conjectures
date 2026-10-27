## Worker report

Item: lem-pur-general-pair-shift-normalization. Group NR. Stage 1 only, 2026-10-27.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-general-pair-shift-normalization.json: split, statement unchanged; five construction and uniqueness steps.
- dag/nodes/sec-smooth-purity/lem-pur-unnormalized-pair-functor-descent.json: statement; not a Mathlib match. The existing project declarations listed below supply the generic descent interface; their names are seeded for maintainer attachment/audit, without setting the audit state to closed ourselves.
- dag/nodes/sec-smooth-purity/lem-pur-coherent-shift-from-core.json: statement; Mathlib leaf, CategoryTheory.hasShiftMk, Mathlib/CategoryTheory/Shift/Basic.lean:153, together with ShiftMkCore.shiftFunctor_eq:204, shiftFunctorZero_eq:208, shiftFunctorAdd_eq:212.
- dag/nodes/sec-smooth-purity/lem-pur-intrinsic-associator-shift-square.json: statement only, not a Mathlib match; the square for the actual intrinsic scalar associator is isolated rather than assumed from a theorem on an older presentation.
- citations.json contains a verbatim part of each cited statement for every step/use pair. searches.jsonl is the original output record of every msearch invocation in this attempt. The small sandbox-only Python scripts generate the JSON; they are not project or launcher edits and are not delivery files.

### Attachments

The item cannot be attached: the exact live theorem WeilConjectures.GeneralAlgebraicallyClosedCoefficients.shift_existsUnique, lean/Sheaf/Paper/GeneralAlgebraicallyClosedCoefficients.lean:534, ends in sorry at line 553. A search for its notion and blueprint id in lean/WeilConjectures and lean/Sheaf found no completed declaration giving its full normalized uniqueness assertion. StageSystem/Shift.lean constructs a shift but does not assert uniqueness of the entire HasShift structure with the required inclusion constraint.

The following names belong to the new generic descent node lem-pur-unnormalized-pair-functor-descent, all in WeilConjectures/CategoryTheory/StageSystem/Functor.lean. I read their source and compared the formulas, including the lack of a unitor axiom and the independent universes. The existing local/sorry_map_slopmaster2_liveb2378f05.jsonl.gz records s=false and ts=false for every one; this is recorded audit evidence, not a fresh compiler run. The new node seeds names with state none so the maintainer can run its own attachment/audit.

- CategoryTheory.StageSystem.Morphism.functor:129, functor_obj:145, functor_map_mkHom:148, tr_mapAt:98.
- CategoryTheory.StageSystem.Morphism.functor_map_ι:160, ιCompFunctorIso_hom_app:174.
- CategoryTheory.StageSystem.Morphism.descNatTrans:212, descNatTrans_app:222, descNatTrans_id:238, descNatTrans_comp:244.
- CategoryTheory.StageSystem.Morphism.descNatIso:251, isIso_descNatTrans:261.
- CategoryTheory.StageSystem.Morphism.functor_id_map:383, functor_comp_map:389.

The descent of whiskering and equations in the node is the component formula plus functor_map_ι, functor_id_map and functor_comp_map, with no further existence assertion. It introduces no second pair-category construction.

### WANTED

None. This is an agent-written construction from the retained blueprint clause, the current generic pair-model proof, and the live source interfaces; no external textbook proof or Stacks theorem is asserted for these project-specific normalizations. No SGA is used.

### What was wrong or missing

The live item was unsplit. Its statement is retained, including arbitrary Y, independent universes, raw rationalization without Karoubi completion, actual quotient/category equality, and full zero/add coherence uniqueness. The latest blueprint's sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md now states finite-coefficient descent and the ordinary two-colimit comparison; the old order-1462 construction is retained in the live DAG ancestor and its live Lean interface. I read that current file and the current sk-def-sfb-filtered-two-colimit/det-def-sfb-filtered-two-colimit-model.proof.md, not an older blueprint snapshot. The latter's Comparison functor calculation supplies the ordinary common-stage descent mechanism, generalized as in the already existing StageSystem/Functor.lean source.

During C4 review I rejected an initial proposed application of lem-weil-scalar-associator-shifts. That node states the square for rationalConstructibleScalarComp with a finite-field datum, whereas the current stages use intrinsic sfRationalScalarComp and its chosen normalization. Parameter independence of functors and their shift structures alone is not an explicit statement identifying these two associators. The delivered proof therefore uses the new intrinsic square node and no auxiliary finite-field datum at all. This is a repair to the proof plan, not a dispute or weakening of the item. Its remaining intended proof route is to verify the ordinary derived tensor associator's signed shift square, lift it through the fully faithful intrinsic integral inclusion with its normalized ordinary/completed comparisons, and descend it through raw rationalization with the prescribed integral-image shift. This route is recorded here as work for that statement-only node, not supplied as an assumed identification.

### Unfinished work

The intrinsic associator square is intentionally left as a searched statement-only node for the next one-level split. The generic descent node has existing project attachment evidence; its audit/attachment is left to the maintainer. No part of the item's uniqueness is moved to a new node. No Lean was written, compiled or built. No repository or launcher file was modified and no git command was run in the read clone.

## Not duplicates

lem-pur-unnormalized-pair-functor-descent vs lem-sbc-coherent-pair-functor-descent: the latter assumes identity transitions and identity repeated-field associators, whereas the new node allows the actual unnormalized self-transitions and independently sized directed index; it asserts the ordinary descent API without shifts or Karoubi completion.

lem-pur-unnormalized-pair-functor-descent vs prop-weil-pbc-descent-functors: the latter is for exact finite rational coefficient functors on the specified PBC categories; applying it here would already assume the pair shifts being constructed, as well as its more restrictive scheme hypotheses.

lem-pur-unnormalized-pair-functor-descent vs lem-sf-framework-common-stage-descent: the latter assumes a finite-field datum and exact functors on coefficient categories whose pair triangulations already exist; the new node applies to arbitrary category systems before any pair shift structure is defined.

lem-pur-unnormalized-pair-functor-descent vs lem-weil-pbc-filtered-colimit-functor-descent: the latter is a strict diagram of small categories with object/arrow set-colimit hypotheses; it does not state a pseudocoherent unnormalized pair formula or natural-transformation descent.

lem-pur-unnormalized-pair-functor-descent vs lem-fd-common-stage-comparison-descent: that node is for exact equivalences of two rational coefficient presentations on allowed noetherian finite-dimensional schemes; this ordinary categorical interface needs none of those data.

lem-pur-coherent-shift-from-core vs def-weil-triangulated-category: the existing definition describes (pre)triangulated categories and their integer powers, and does not state the Mathlib core construction with its precise data equalities.

lem-pur-intrinsic-associator-shift-square vs lem-weil-scalar-associator-shifts: the latter names the old rationalConstructibleScalarComp and a finite-field datum; the new node names the actual intrinsic tensor associator on arbitrary Y, using the independent-universe small coefficient models and exact normalized sigma of the item. The missing identification was not used.

lem-pur-intrinsic-associator-shift-square vs lem-pur-general-intrinsic-finite-field-transport: the latter assumes a finite-field datum and concludes a whole package including pair shift uniqueness; it is not a smaller antecedent for constructing the datum-free package. The new node is only a finite-stage natural-transformation square and assumes no pair shift.

lem-pur-intrinsic-associator-shift-square vs lem-sf-strict-direct-image-scalar-comparison: that node concerns normalized scalar/direct-image comparison maps and their cocycle on separated finite-type schemes over k, not scalar associator shift compatibility.

Before creating nodes I searched the entire DAG's statements/titles for stage-system morphisms, compatible transformation families, coherent shifts and associators; searched all DAG files for StageSystem.Morphism, descNatTrans, hasShiftMk, ShiftMkCore and scalar comparator names; and read the closest statements listed above. Whole-blueprint searches via tools/blueprint_refs.py included stage system, coherent integer, stagewise shift, functor descent, ShiftMkCore, compatible families, zero and addition, common-stage pair, and scalar associator. None gave these interfaces with the required hypotheses. No Stacks tag is attached to these project-specific nodes, so there are no same-tag duplicate pairs to suppress.

## Review by NR

I read the item source signature/docstring at GeneralAlgebraicallyClosedCoefficients.lean:508-553, the generic construction StageSystem/Shift.lean:48-243, the scalar stage definitions in GeneralAlgebraicallyClosedCoefficientStages.lean, the current two-colimit blueprint unit and generic pair-model proof, and every cited node's statement. The item source's two representative equalities use HEq: the JSON's literal object identifications and representative formula retain precisely this interpretation. I did not replace equality of structures by equivalence of categories.

For the new descent node I read StageSystem/Functor.lean:56-395 and Basic.lean's pair and inclusion formulas. Its tower equation is Morphism.coh, with right-to-left categorical composition; its transport formula is tr_mapAt. The source permits repeated indices without a normalized T_ii. The transformation compatibility equation is Hom.comm; its components are j_i(eta_i). This genuinely general tool does not assert a shift, additivity, a cone or any uniqueness part of the item. The source shows its inclusions have identity comparison components. The live sorry-map evidence was checked by exact full names and all fourteen have neither direct nor transitive sorry. I leave the state update to the maintainer.

For the Mathlib leaf I read Basic.lean:64-87,119-155,204-214. The three core coherence equations in the statement are exactly the fields assoc_hom_app, zero_add_hom_app and add_zero_hom_app, with the object-equality casts retained. hasShiftMk has independent category object, category hom and monoid universes; the displayed comparison equations are rfl. The leaf claims existence with prescribed data, not generic uniqueness. The Mathlib queries returned this declaration, which was then checked in source. No new definition of HasShift is introduced.

For the intrinsic square node I read the normalized associator definition in GeneralAlgebraicallyClosedCoefficientStages.lean and the item docstring's required compatibility. Its source is the scalar part of the retained common-stage construction, not a claim that the blueprint's ordinary 2-colimit statement proves the intrinsic square. I also opened the old scalar-associator node and read its statement, which caused the C4 correction above. The new node states exactly the square between T_LM T_EL(K[n]) and (T_EM K)[n], without assuming a structure map on Y or a finite-field datum. Its independent proof obligation is essential to shift well-definedness; it is not the item's shift-existence or uniqueness clause repackaged.

Step 1 cites only the new intrinsic square and general descent statement. Their two tower formulas have the same orientation under Phi_E=[n] and b_EL=sigma_EL. Step 2 cites descent for well-defined functors, the Hom-coordinate lemma for finite representatives and actual sums, the stage lemma for the supplied normalized stage data, and the triangulated definition for additive shifts and additive-category Hom laws. Conjugation distributes over addition, so no abstract colimit-preserves-additivity theorem is silently used.

Step 3 cites descent for natural transformations, composition, inverse pairs and equations, the stage lemma for coherent transition comparisons, and the core leaf for packaging. The two unit and one associativity equations are written out at (E,K), where Q_d j_E=j_E[d] makes them the images of the stage equations. The naturality of the zero/add maps is not asserted merely because they have components: it is the transformation-descent conclusion, whose transition compatibility hypotheses are exactly the CommShift zero/add equations. All n,m,d are integers, including zero and negatives.

Step 4 is elementary relative to descent and the constructed components: identity beta's naturality is equality on the stage inclusion, and its zero/add equations are those displayed component definitions. Step 5 is elementary extensionality relative to the cited representative lemma, literal-pair definition and core description: the common formula identifies every functor, identity beta forces z and c at every pair, and then the monoidal functor's epsilon and tensorator are their uniquely determined inverses. Equality of the remaining proof fields follows from proof irrelevance. It neither assumes the inclusions are faithful nor promotes a natural isomorphism to equality without identifying object and arrow data. There is no independently quantified gauge left on the coherence maps.

I tested the generic descent statement with one index and T_ii only isomorphic to an identity, with repeated indices, and with identity families. Its lack of an extra unitor hypothesis agrees with the existing source. I tested the core statement with the zero monoid and with noncommutative additive monoids: the order c_(a,b):F_(a+b) -> F_b F_a is preserved, and nothing claims autoequivalences for a monoid without inverses. I tested the intrinsic square with E=L=M and n=0, with n and -n, with the zero object, and with empty Y; each is a coherent tensor/shift square with unchanged endpoints, not an assertion of literal tensor identity. Arbitrary nonnoetherian Y and independent universes are kept throughout. The new statements do not hide proofs, and no step exceeds 2000 characters. B1-B10, C1-C8, D1-D5 and E1-E7 were checked against these concrete statements; the substantive repair was the old/intrinsic scalar-associator distinction. There was no second worker or delegation, as required by the direct-delivery brief.

Dry-run metadata repair: added the existing def-nagata-category and def-sfb-monoidal-category citations to the core leaf after reading their statements, and populated mathlib_match.line=153 (the pinned source declaration read above). These are statement notions, not additional proof assumptions; the leaf comparison and equations are unchanged. Updated the affected verbatim citation quotes.
