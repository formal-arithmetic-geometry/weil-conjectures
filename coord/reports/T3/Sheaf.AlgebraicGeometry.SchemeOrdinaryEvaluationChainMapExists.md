## What changed

Completed the proof of `AlgebraicGeometry.schemeOrdinaryEvaluation_chain_map_exists`
in `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationChainMapExists`, with its original
signature and visibility unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation`.
The new module constructs `schemeOrdinaryEvaluationGradedComponent` by symmetry and inverse
tensor-Hom adjunction of the fixed Hom projection, and
`schemeOrdinaryEvaluationGraded` by coproduct descent. These are explicit definitions,
not data chosen from an evaluation-existence theorem.

The main proof sets U equal to the already constructed resolved uncurrying. The new
coefficient identity gives U_n = E_n followed by eta_n. The fixed augmentation eta is
monic by `monoQuasiIso_toKInjectiveResolution_app`, and its degree components are monic.
Postcomposing the differential equation for E with eta_m, the chain equations for eta
and U identify both sides. Cancellation proves differential compatibility, and the
explicit degree maps therefore define a chain map. Complex extensionality proves the
required factorization. Updated the original node's proof and dependencies accordingly.
No existing definition or interface was changed and no other existing module was adapted.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeOrdinaryEvaluation_chain_map_exists`
(node `lem-pc-scheme-ordinary-evaluation-chain-map-exists`). No sorry remains in that module.
Added exactly one hole:
`AlgebraicGeometry.schemeOrdinaryEvaluationGraded_augmentation`
(node `lem-pc-scheme-ordinary-evaluation-graded-augmentation`), in
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation`.
This is a decomposition: one hole closed, one added, net zero. The new theorem is only
coefficient compatibility of explicitly defined graded maps, for arbitrary coefficients N;
it neither constructs a chain map nor asserts any differential equation. The main proof
supplies those missing steps by genuine Lean cancellation and assembly.
The two new definitions contain no sorry. The new component helper was renamed during second reading to avoid a collision with the existing scheme ordinary evaluation component. Their projections come from the already proved
product-projection construction and its uniqueness, rather than arbitrary existence data.

Both modules compile cleanly with `lcompile.py --all`; the new module takes about 8 seconds
and the main module about 8 seconds. No boundedness or nonvanishing hypotheses were added.
The empty scheme and zero complexes require no exceptions: all constructions and equations
are coproduct/adjunction identities, and monicity is supplied for every complex.

## No longer needed

No original import removed; no named nodes or modules pruned. A second direct calculation
of Koszul signs for ordinary evaluation is unnecessary: the existing resolved uncurrying
chain equation and monicity of the augmentation suffice. The original Hom projection,
tensor-closed, and uncurrying differential nodes remain needed, now partly through the new
coefficient identity. The existing proved K-injective functorial existence node supplies
monicity. The unit's own statement and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Second reading found and repaired a public-name collision in the new helper; see the final review section. The original plan can be shortened below the unit level by
cancelling the fixed monomorphic augmentation instead of repeating the signed differential
calculation. The remaining coefficient step is mathematically the projection naturality
formula plus the naturality of inverse tensor-Hom adjunction and coproduct extensionality.

For the next worker: generic site-level versions of the projection and inverse-adjunction
naturality formulas were successfully proved during exploration. The unresolved glue was
matching their specialized scheme equation to the exact component selected by
`schemeTensorHomUncurry_component` and `mapBifunctorDesc`, with the scheme-specific implicit
site instances and chosen projection witnesses. Attempts to finish that bridge produced
a type mismatch under strict transparency; aggressive conversion unfolded the large chosen
Hom-complex witness and exceeded the single-file limit. These temporary attempts are not
in the delivered modules. `homComplex_projections_exists` selects definitionally the same
projection family as `Classical.choose (Classical.choose_spec (homComplex_exists ...))`;
use that small projection API and avoid unfolding the whole chosen Hom-complex functor.
`SheafOfModules.tensorHomEquiv_comp_homObjMap` proves inverse-adjunction naturality by
injectivity of the tensor-Hom equivalence. The existing generic calculation in
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality` is also useful,
although its internal helper is private. The new node and docstring specify the full
remaining argument, independently of these implementation hints.

## New nodes

`lem-pc-scheme-ordinary-evaluation-graded-augmentation` isolates coefficient compatibility
of explicit degreewise evaluation with a map into the fixed resolution. Its module is
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation`; its source is the
original ordinary evaluation calculation (Stacks cohomology.tex, Tags 08DJ, 08DM, 08DQ).
The proof uses only the Hom projection naturality, coefficient naturality of tensor-Hom
adjunction, and coproduct summand equations. It needs no monicity or differential equation.
It is strictly part of the original argument and retains its chapter and blueprint unit.
No change records are required because existing interfaces are unchanged.

## Second reading by T3

1. **Statements and interfaces.** Compared both delivered modules with the repository versions. The target theorem signature and all existing declarations are unchanged byte for byte; the added theorem has a narrower degreewise coefficient-compatibility statement and does not restate the target. Verdict: pass.

2. **Proof and trust basis.** Compiled both modules together with `lcompile.py --all`; compilation succeeds. The target proof has no `sorry`, and the only remaining `sorry` is the named split theorem `schemeOrdinaryEvaluationGraded_augmentation`. No forbidden declarations or hollow definitions were found. `#print axioms` on a scratch import of all four declarations confirmed: both explicit definitions use only `propext`, `Classical.choice`, and `Quot.sound`; the target and the split theorem additionally use `sorryAx`. Verdict: pass, with the documented split hole remaining.

3. **New statement and search.** The split theorem is true by coproduct extensionality, projection naturality, and tensor-Hom coefficient naturality; it is strictly weaker than the target and needed by the cancellation proof. Independent searches used `tensorHomEquiv_comp_homObjMap|ι_mapBifunctorDesc|ev_naturality` (grep), inverse tensor-Hom coefficient postcomposition (LeanFinder), and `HomologicalComplex.mapBifunctorDesc` (Loogle), as well as repository `rg`. They supply component and coproduct APIs but no existing declaration with this statement. Zero g gives zero on both sides by additive Hom and adjunction; zero complexes and the empty scheme preserve the same equations. No boundedness, monicity, or nonzero hypothesis is required by the split identity. Verdict: pass.

4. **Pruning and route.** The proof uses the explicit graded evaluation construction, the existing uncurrying differential theorem, projection API, and monomorphic K-injective resolution. The existing public import is needed by the signature; the new proof import is needed by the coefficient identity; the split module’s public projection import is needed by the explicit component definition; the unit route is retained. The unit record `dag/units/sk-thm-picard-duality.json` has empty `realized` lists and was left unchanged; this below-unit reduction retains evaluation and coefficient compatibility. Verdict: pass.

5. **DAG agreement.** Updated proof, proof dependencies, and proof origin match the Lean proof. The new node records the split theorem, its source, declaration, and dependencies. Verdict: pass.

Second reading found a public-name collision with the existing `AlgebraicGeometry.schemeOrdinaryEvaluationComponent` in `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationComponent`. Renamed the new helper to `schemeOrdinaryEvaluationGradedComponent` and its use in coproduct descent. Existing library interfaces remain unchanged. An exploratory attempt to close the split theorem encountered the reported scheme-site transparency mismatch and was removed; the documented named split hole remains.
