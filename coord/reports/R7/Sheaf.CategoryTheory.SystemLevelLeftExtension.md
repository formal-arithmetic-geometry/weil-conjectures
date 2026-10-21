## What changed

Proved `SheafOfModules.systemLevelLeftExtensionTheory` in
`lean/Sheaf/CategoryTheory/SystemLevelLeftExtension.lean`, with its statement unchanged.
The proof constructs every field of the original theory record for arbitrary sheaf-ring
sequences; no coefficient flatness, boundedness, or normalization hypothesis was added.

The 39 new Lean modules contain fully proved components: explicit ringed-sequence-site
and strict-system equivalence, coefficient-universe Grothendieck and coproduct results,
actual ordinary singleton and subsequence tensor extensions, simultaneous flat-term
K-flat representatives, normalized derived extension data, evaluation comparisons,
actual derived transitions, and both final adjunction-mate coherence equations.
The original 50 named public signatures and all original structure fields are unchanged.
Definitions are publicly reexported from `SystemLevelLeftExtensionBasic` and
`SystemScalarModel` to avoid a definition/proof import cycle; the change record is
`coord/changes/system-level-left-extension-foundations-R7.md`.

The actual derived scalar associators and composition map are defined by adjoint uniqueness.
Their normalized mate equations prove transition and composition coherence on all derived
objects directly. They require neither a diagram-category identification of the derived
system category nor a second K-flat preservation argument for iterated extension.

Validation: all 40 packet Lean modules compiled in import order without warnings or
errors, through `lcompile.py --all`, including the final theorem. No declaration in the
packet contains `sorry`. Temporary profiling localized the definition-elaboration cost; no profiler settings remain.
The latest full foundation checks completed in 51.5 and 52.9 seconds, within the unchanged
60-second limit. Consumer signatures were audited by `tools/downstream.py`, comparison
of all 50 original headers and structure records, and preservation of every old public import.
The initial 28 downstream modules were compiled unchanged against the packet. After a
concurrent coefficient-image delivery, its five new/changed modules were checked too,
covering all 32 current downstream modules without adapting any consumer. One batch run
exceeded 60 seconds in `CoefficientSystemDerivedComparison`; its unchanged single-file
check then passed in 33.0 seconds (29.2 seconds against the published library).
The final delivery also runs its compile, preflight and declaration checks.

## Proved and sorry left

Closed 1 original hole: `SheafOfModules.systemLevelLeftExtensionTheory`
(node `lem-pur-system-level-left-extension`). Original item count: 1; remaining: 0.
Added 0 holes, split off 0 unproved statements. All 40 new nodes below are proved,
including every constructor and the final selected-transition and composition-evaluation
identities. This is a proof of the item from existing library declarations, not a
relocation of its hole. Existing upstream assumptions and holes remain those of the
imported library and are not counted as proofs by this packet.

## No longer needed

No Lean module or adopted source declaration is withdrawn, and no `deleted.txt` is used.
The item had no separate proof imports to delete. Its former monolithic public foundation
imports are supplied by the new public foundation module with the same declarations.

Removed unused template imports from the new modules:

- `SystemDerivedSubsequenceTransition` and `SystemDerivedSubsequenceEvaluationComposition`:
  `DerivedCategory.ExactRestrictionComposition`,
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
- `SystemDerivedSubsequenceEvaluationComposition`: `SystemDerivedTransition`.
- `SystemDerivedTransitionCoherence`: `SystemDerivedSubsequence` and both WeilConjectures
  imports listed above.
- `SystemDerivedTransitionUnit`: both WeilConjectures imports listed above.

These files use the existing evaluation/transition APIs and their public dependencies.
Proof-only imports of the Grothendieck, coproduct, scalar-generator, and generic mate
helpers are private. The evaluation-topos import remains public because its additive
instance is needed by the K-flat declaration's complex-functor signature. No dependency needed for an actual signature or
construction was removed.

The following old planned proof-dependency wrappers are not imported by the new route:

- `lem-weil-pbc-module-sheaves-colimits-forgetful` / `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `lem-weil-pbc-ringed-topoi-module-adjunction` / `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `lem-weil-pbc-exact-functor-derived-functor` / `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `lem-pc-derived-adjoint-functors` / `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `lem-pc-pre-derived-adjoint-functors-general` / `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction` / `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.

Componentwise colimits are constructed directly; ordinary tensor adjunctions use the
existing normalized coefficient interface; exact derived functors use the Mathlib
localization API; the existing normalized derived Hom comparison replaces the longer
wrapper chain for deriving adjoints. Mathlib leaves for exact factorization, homotopy
exactness and mate pasting are still used through their actual Mathlib declarations.

The obsolete enhanced/model-category approval entries removed from this node are
`lem-coef-sheaf-flat-model`, `lem-weil-pbc-site-flat-quotient-tensor-ses`,
`lem-coef-quillen-section-rectification`, `lem-coef-dg-derived-quillen-calculus`,
`lem-coef-semilinear-derived-sections`, and `lem-coef-pointed-model-stability`.
The five unused generic wrapper approvals corresponding to the list above are also
removed, without adding or reordering any maintainer approval. No enhanced section
rectification, dg calculus, pointed-model stability, or model-category suspension
calculation enters this proof.

Do not prune the original K-flat resolution, ringed-topos K-flat pullback,
resolving-class, pointwise bridge, termwise adjunction, or sheaf-tensor dependencies:
the new proof still reaches their existing declarations. In particular the adopted
ringed-site Grothendieck theorem remains imported by existing upstream proofs even
though the universe-correct direct system proof uses the new coefficient-universe lemma.
The unit route is retained; only work below the unit has been reorganized.

## Where the brief, the DAG or earlier work was wrong

The original statement is true, and no statement is disputed or weakened. The old
ordinary-derived plan was mathematically sound but left implementation glue unstated:
the explicit strict-system/ringed-site equivalence, simultaneous K-flat representatives,
comparison passage between cochain and homotopy categories, and normalized nonexact
left-adjoint evaluation mates. The existing adjoint-square theorem requires exact ordinary
left adjoints and cannot be applied to arbitrary coefficient tensor extension. The new
generic mate calculation uses the normalized left-derived comparisons and exact right
functors instead. The ringed-site Grothendieck application also needs a generator indexed
in the coefficient universe, rather than an extra inequality on presentation universes.

For the last two coherence equations the plan's twice-resolved representative calculation
can be replaced by right-square pasting and adjoint uniqueness. This shorter argument
proves the exact specified associators and extension mate, including equal selected
indices and the dependent equality transport for composite selections. No source-library
boundary exception or consumer adaptation was used.

## New nodes

`lem-pur-adjunction-evaluation-composition`: Evaluation and composition of normalized adjunction mates. Fully proved; its attached module is `AdjunctionEvaluationComposition`. Compare inverse isomorphisms, transpose through L3⊣R3, and apply the composite transpose formula. The three evaluation normalization equations express the result in terms of the units of F and G. Naturality of γ1 moves the intermediate G-unit into the first evaluation. The right-square pasting equation inserts δe; adjoint uniqueness identifies the transpose of the inverse extension compositor with the composite unit. Injectivity of the Hom equivalence and equality of inverses prove the assertion.

`lem-pur-adjunction-mate-transpose`: Transpose formula for a general mate square. Fully proved; its attached module is `AdjunctionMateTranspose`. Expand the mate at the first adjunction unit, then use naturality in the target of the second Hom equivalence. The unit-mate identity and naturality of τ replace the composite by G applied to the first unit followed by R1(f), which is exactly the first transpose.

`lem-pur-adjunction-transition-coherence`: Transition coherence for evaluation mates. Fully proved; its attached module is `AdjunctionTransitionCoherence`. Precompose with the inverse upper evaluation and inverse first associator, and transpose through Lt⊣Rt. Each inverse associator becomes its right restriction compositor by adjoint uniqueness. Apply the two normalized evaluation equations. The right-square composition law and naturality of τk with respect to the extension unit make both transposes equal. Cancel the two invertible precomposing maps.

`lem-pur-cochain-adjunction-compatibility`: Normalized derived Hom formulas on cochain complexes. Fully proved; its attached module is `CochainAdjunctionCompatibility`. Factor the cochain localization through the homotopy quotient. Apply the prescribed homotopy transpose formula to the quotient of the chain map. The quotient-to-derived comparison and the termwise adjunction quotient compatibility identify each side with its cochain version; cancellation of the identity comparison completes the calculation.

`lem-pur-cochain-homotopy-derived-comparison`: Comparison through the homotopy quotient. Fully proved; its attached module is `CochainHomotopyComparison`. Transport the comparison along the natural factorization through the homotopy quotient. The quotient localization makes its components independent of the chosen cochain representative. The left derived universal property transfers across this localization and its canonical factorization isomorphisms, giving existence and uniqueness of the homotopy comparison.

`lem-pur-derived-mate-comparison`: Cochain representative formula for normalized derived mates. Fully proved; its attached module is `DerivedMateComparison`. Transpose through the second derived adjunction. The derived right square representative equation and the two normalized Hom formulas identify the transpose with localization of the ordinary unit-mate equation. Naturality moves the comparison maps past the ordinary unit. Injectivity of the Hom equivalence proves equality.

`lem-pur-exact-derived-coproducts`: Coproduct preservation by exact derived functors. Fully proved; its attached module is `ExactFunctorCoproducts`. Use the known coproduct cocone of the derived category obtained from termwise coproducts of complexes. Any family of derived objects is represented by a family of complexes. The exact functor factorization identifies its image cocone with localization of the termwise image coproduct; the ordinary preservation hypothesis and localization preservation make this a coproduct. Transport through the representing family isomorphisms.

`lem-pur-exact-restriction-composition`: Exact restriction compositors and their localization formulas. Fully proved; its attached module is `ExactRestrictionComposition`. Expand the derived comparison as the inverse exact-functor compositor followed by localization of η. Its factorization equations cancel the two successive exact factorization isomorphisms. The identity comparison formula follows through the homotopy quotient; all quotient comparison components are identities. Cancel forward and inverse unit factors to obtain the inverse formula.

`lem-pur-extension-evaluation-comparison`: Evaluation comparison for derived left extensions. Fully proved; its attached module is `ExtensionEvaluationComparison`. The normalized derived mate representative formula identifies its cochain value, after multiplication by comparison maps, with localization of the ordinary isomorphism. On p1 the two left comparison maps are invertible, so the mate is invertible. Every derived object has a quasi-isomorphic p1 representative; naturality transports invertibility to it. Take the inverse mate and apply the general mate-transpose formula.

`lem-pur-normalized-adjunction-composition`: Composition and uniqueness of normalized adjunction formulas. Fully proved; its attached module is `NormalizedAdjunctionComposition`. Transpose successively through the two Hom equivalences. Naturality in the source moves the first left comparison outside the second transpose, and naturality in the target moves the second right comparison outside the first. For uniqueness, apply the transferred Hom equivalence to both candidate maps and use its unit normalization. Expand the composite Hom equivalence to obtain the general composite adjunct formula.

`lem-pur-normalized-left-extension`: Normalized left extension from a resolving class. Fully proved; its attached module is `NormalizedLeftExtension`. Apply the existing left-derived-from-resolving-class theorem to E. Pass its comparison through the homotopy quotient. The existing normalized derived adjunction theorem for an exact right functor supplies the derived Hom bijection. Transfer the formula back to cochains. Uniqueness of the universal left derived comparison identifies the pointwise and triangulated constructions; package the derived data while retaining the ordinary functor and adjunction definitionally.

`lem-pur-ringed-site-grothendieck-coefficient-universe`: Grothendieck module categories at the coefficient universe. Fully proved; its attached module is `RingedSiteGrothendieckCoefficientUniverse`. Use the small model of C to index a small family of free sheaf-module generators. The existing free-module generating property detects maps after transfer through the small-model equivalence. Filtered colimits are exact because the exact conservative forgetful functor to abelian sheaves creates them. Package AB5 and the small generator family to obtain the Grothendieck property.

`lem-pur-system-coproducts`: Coproducts and derived evaluation for strict systems. Fully proved; its attached module is `SystemCoproducts`. Componentwise construction gives ordinary coproducts and exact evaluation. The Grothendieck property supplies K-injective resolutions for the system and level categories. Apply the existing Grothendieck derived coproduct construction, and the exact derived functor preservation theorem, to each evaluation.

`lem-pur-system-derived-evaluation`: Cohomology and joint detection by system evaluations. Fully proved; its attached module is `SystemDerivedEvaluation`. Apply exact functor compatibility with homology. A strict system is zero exactly when each component is zero, so componentwise homology detects acyclicity and each cohomological bound. In an abelian derived category the cone criterion and homology detection characterize isomorphisms. Finally quasi-isomorphisms are exactly the maps inverted by Q, and the exact evaluation factorizations transfer this criterion to components.

`lem-pur-system-derived-subsequence`: Canonical exact derived subsequence comparisons. Fully proved; its attached module is `SystemDerivedSubsequence`. The corresponding ordinary functor composites agree definitionally. Take the inverse of the exact-functor derived compositor. Cancel it against the forward compositor in the factorization equation to obtain both representative formulas.

`lem-pur-system-derived-subsequence-evaluation-composition`: Subsequence evaluation respects restriction composition. Fully proved; its attached module is `SystemDerivedSubsequenceEvaluationComposition`. Check equality after localization on complexes and cancel the final exact evaluation factorization. Expand the restriction compositor and selected evaluation representative equations. Naturality of the second evaluation comparison moves the first restriction factorization past it. Both sides then consist of the same three successive exact factorization maps.

`lem-pur-system-derived-subsequence-transition`: Subsequence evaluation respects derived transitions. Fully proved; its attached module is `SystemDerivedSubsequenceTransition`. Check after localization and postcompose with the invertible evaluation and scalar restriction factorizations. Use the transition and selected evaluation representative equations. Naturality moves the subsequence factorization across the transition. The strict transition of the subsequence is definitionally the original selected transition in every term and on sections.

`lem-pur-system-derived-transition`: Localization of actual semilinear transitions. Fully proved; its attached module is `SystemDerivedTransition`. Lift the strict cochain natural transformation through localization and compose with the exact functor compositor for evaluation followed by scalar restriction. Apply the formula for localization of a natural transformation and the exact compositor factorization. The inverse factorization cancels its forward map.

`lem-pur-system-derived-transition-coherence`: Derived semilinear transitions compose. Fully proved; its attached module is `SystemDerivedTransitionCoherence`. Use localization uniqueness and postcompose with invertible target evaluation and restriction factorizations. The canonical restriction compositor has the forward factorization formula. Naturality of restriction factorization and the two transition representative formulas reduce both sides to Q of the strict composition law, which holds termwise on sections.

`lem-pur-system-derived-transition-unit`: Identity transitions and the canonical derived tensor unit. Fully proved; its attached module is `SystemDerivedTransitionUnit`. Localize the strict identity law and cancel the exact target factors. The inverse restriction unit factorization gives the identity transition formula. The canonical derived tensor unit is the left-adjoint uniqueness isomorphism against the identity adjunction; its normalized Hom formula says its transpose becomes identity after the restriction comparison. Cancel that comparison.

`lem-pur-system-evaluation-kflat`: Simultaneous componentwise K-flat representatives. Fully proved; its attached module is `SystemEvaluationKFlat`. Construct evaluation as the inverse image of the geometric morphism of the sequence site, with identity structural ring map. Apply the existing ringed-topos K-flat and flat-term pullback theorem. Resolve the module complex on the single ringed sequence site by a flat-term K-flat complex, then transport the augmentation and its quasi-isomorphism back along the explicit strict-system/module equivalence. Exactness of the equivalence and all evaluations gives the simultaneous property.

`lem-pur-system-evaluation-topos`: Evaluation as inverse image on the ringed sequence site. Fully proved; its attached module is `SystemEvaluationTopos`. The vertical-cover description proves continuity and cocontinuity. Comma categories for vertical evaluation have small models, giving the needed right Kan extension. Identify inverse image with sheaf composition by the standard site adjunction, and identify module evaluation with restriction along the identity ring map. Sectionwise module linearity and componentwise colimit and limit formulas establish additivity and exactness, including both equivalence functors.

`lem-pur-system-grothendieck`: Grothendieck abelian strict-system categories. Fully proved; its attached module is `SystemGrothendieck`. Use the explicit equivalence with modules on the small ringed sequence site. Apply the Grothendieck module-category theorem at the coefficient universe there, and transport the Grothendieck property through the equivalence.

`def-pur-system-level-left-extension-basic`: Strict systems and the unchanged left-extension interface. Fully proved; its attached module is `SystemLevelLeftExtensionBasic`. The category laws hold componentwise. Kernels are computed on sections; cokernels and arbitrary small colimits are obtained by componentwise sheaf-module colimits, with transition maps induced by their universal properties. The resulting abelian structure and evaluation exactness agree with the original normalized structures. A map and a zero object are detected by their components. Strictly increasing natural-number embeddings are unbounded, so minimum selected indices exist; minimality proves monotonicity and composition of these indices. The remaining structures are explicit records of the same normalized adjunction and tensor statements.

`lem-pur-system-ordinary-selected-extension`: Ordinary subsequence left extension with actual transitions. Fully proved; its attached module is `SystemOrdinarySelectedExtension`. Use minimum selected indices and their monotonicity. Define transitions by scalar adjunction and tensor associators. On a local pure tensor c⊗x the transition is the image of c times the actual transition of x; unit tensor generators detect equality, proving identity, composition and naturality. At r(i), t(r(i))=i and the scalar tensor unit gives the unit of the subsequence adjunction. Construct the inverse Hom map componentwise by scalar transposition. Commutation, and the two inverse identities, follow on tensor generators from the strict system composition law. Evaluation at each level verifies additivity.

`lem-pur-system-ordinary-single-extension`: Ordinary singleton left extension. Fully proved; its attached module is `SystemOrdinarySingleExtension`. Construct the tensor transition below n by scalar adjunction and the canonical associator, and use the unique zero map in the remaining cases. Tensor generators and the ring functor composition law prove the system laws. At n the inverse tensor unit supplies the adjunction unit. Given P→M_n, take its composite with each transition and scalar-transpose it below n, and use zero above n. The strict composition law proves the system-map equations. Transposing at n and checking tensor generators proves the inverse Hom identities; componentwise tensor additivity proves additivity.

`lem-pur-system-ringed-sequence-site`: Strict systems as modules on one ringed sequence site. Fully proved; its attached module is `SystemRingedSequenceSite`. The existing coefficient-sequence topology describes sheaves exactly as vertically sheaf presheaves. Define the ring restrictions from B and its vertical sheaf condition levelwise. A strict system gives a module presheaf by composing horizontal semilinear transitions with vertical restrictions; the strict system laws prove functoriality and vertical sheafness gives sheafness. Conversely restrict a module sheaf vertically and obtain transitions from horizontal arrows. The coefficient ring naturality makes them linear over restriction. Unit and counit are identity maps on sections, proving the explicit equivalence and its triangles.

`lem-pur-system-scalar-coherence`: Canonical scalar tensor unit and associators. Fully proved; its attached module is `SystemScalarCoherence`. Construct restriction unit and composition isomorphisms sectionwise. Transpose the left-adjoint uniqueness maps and use the normalized unit on x↦1⊗x to prove the pure-tensor formulas. Compose the normalized derived transpose equations and apply uniqueness with the canonical exact restriction comparisons. Degreewise the ordinary uniqueness equation is the same unit equation; localization of that equation proves the derived cochain representative formulas.

`lem-pur-system-scalar-derived-extension`: A scalar model as normalized derived extension data. Fully proved; its attached module is `SystemScalarDerivedExtension`. Fill the record using the scalar model and its universal left derived property. The existing resolving-class theorem supplies pointwise existence and an exact triangulated model; uniqueness of the universal left derived comparison transfers shift and triangulated data to the chosen tensor model. The remaining normalization is the scalar model transpose formula.

`lem-pur-system-scalar-generators`: Unit tensor generators for scalar extension. Fully proved; its attached module is `SystemScalarGenerators`. Apply injectivity of the ordinary tensor-restriction Hom equivalence. Its transpose evaluates x as the map applied to the normalized unit 1⊗x, so the given generator equality makes the transposes equal on all sections. For functoriality use naturality of the unit; scalar linearity supplies the formula for arbitrary c.

`lem-pur-system-scalar-model`: Normalized scalar models for arbitrary sheaf-ring maps. Fully proved; its attached module is `SystemScalarModel`. Use the existing independent-coefficient derived change-of-rings cochain model and the existing sheaf-ring coefficient adjunction normalization. The ordinary unit is the explicit local map x↦1⊗x, and the cochain transpose formula is exactly the normalized derived coefficient adjunction. Package these specified data without choosing an arbitrary existence witness for an ordinary tensor object.

`lem-pur-system-selected-derived-composition`: Canonical composition of derived subsequence extensions. Fully proved; its attached module is `SystemSelectedDerivedComposition`. Transfer the composite adjunction along the canonical exact restriction compositor and take its left-adjoint uniqueness isomorphism to the composite-selection adjunction. The inverse uniqueness map is the forward comparison for the reversed pair. Its Hom normalization identifies the transpose with the composite Hom equivalence; expanding that equivalence gives the stated mate formula.

`lem-pur-system-selected-derived-composition-evaluation`: Evaluation of the derived subsequence compositor. Fully proved; its attached module is `SystemSelectedDerivedCompositionEvaluation`. Reindex composite evaluation to c=t_s(t_r(m)). Its transpose normalization remains the original normalization by equality transport. The selected-evaluation compositor equation, subsequence-transition equation, and actual transition composition law show that the three right evaluation squares paste with the scalar restriction compositor. Apply the general evaluation-composition theorem for normalized adjunction mates. Its uniqueness comparison is the specified extension compositor; the scalar comparison is the canonical tensor associator. The reindexing lemma inserts exactly the equality transport in the conclusion.

`lem-pur-system-selected-derived-evaluation`: Derived evaluation of the subsequence left extension. Fully proved; its attached module is `SystemSelectedDerivedEvaluation`. The right selected-evaluation square is exact selected evaluation followed by the actual derived transition. Its cochain representative is the same strict transition by the two factorization equations. The ordinary tensor comparison satisfies the unit-mate identity by the ordinary selected transpose theorem. The simultaneous componentwise flat-term K-flat resolving class is sent by evaluation into the scalar resolving class. Apply the general normalized evaluation-mate isomorphism theorem and its Hom transpose formula.

`lem-pur-system-selected-derived-evaluation-index`: Reindexing the selected derived evaluation comparison. Fully proved; its attached module is `SystemSelectedDerivedEvaluationIndex`. Substitute the equality of indices. All coefficient inequality proofs coincide by proof irrelevance. The comparison is then the original one, and the transport is the identity, giving both its Hom formula and its component equation.

`lem-pur-system-selected-derived-extension`: Deriving the ordinary subsequence extension. Fully proved; its attached module is `SystemSelectedDerivedExtension`. At each level the ordinary comparison identifies the extended map with scalar extension of the corresponding selected component. Independent K-flat change of rings preserves its quasi-isomorphism. Componentwise detection gives a quasi-isomorphism of systems. Simultaneous flat-term K-flat representatives resolve every strict complex, so apply the general normalized resolving-class left extension theorem.

`lem-pur-system-selected-derived-transition`: The specified tensor-adjoint selected derived transition. Fully proved; its attached module is `SystemSelectedDerivedTransition`. Apply the general transition coherence theorem to the selected derived adjunction and its evaluation comparisons. Their normalized Hom equations at the identity give the two required unit-transpose equations. The actual derived transitions compose, and selected evaluation commutes with transitions, so the right cocone composition equation holds. Canonical tensor coherence was defined by exactly these scalar adjoint-uniqueness comparisons. Thus the generic mate equation is the displayed selected transition formula.

`lem-pur-system-single-derived-evaluation`: Derived singleton evaluation below and above the input level. Fully proved; its attached module is `SystemSingleDerivedEvaluation`. The ordinary below-level tensor comparison and actual transition satisfy the unit-mate identity. Apply the general normalized evaluation-mate theorem with identity source evaluation and the flat-term K-flat resolving class. For vanishing, choose such a representative of the input; its ordinary singleton extension is zero at every term above n. The derived comparison and exact evaluation factorization identify evaluation with localization of this zero complex.

`lem-pur-system-single-derived-extension`: Deriving the ordinary singleton extension. Fully proved; its attached module is `SystemSingleDerivedExtension`. Below n, the ordinary tensor comparison identifies each map with a scalar extension of a quasi-isomorphism between independent K-flat complexes; above n it is a map between zero complexes. Scalar change of rings preserves the former quasi-isomorphisms and the latter are automatic. Componentwise detection proves the system quasi-isomorphism. The independent-coefficient flat-term K-flat resolution theorem gives the resolving class, and the generic normalized left-extension construction applies.

`lem-pur-system-tensor-coherence`: the explicit canonical tensor-coherence record and
its inhabitedness, in `SystemLevelLeftExtensionBasic`. Fully proved from the scalar
coherence construction and functoriality of each ring sequence.

All new nodes have exact Lean attachments, complete proof text, sources, three kinds of
Mathlib search, unchanged chapter/unit membership, and the original adic-stage blueprint
ancestor. Their dependency graph is acyclic. The interface-extraction change record is
`coord/changes/system-level-left-extension-foundations-R7.md`.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
