## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.picard_termwise_target_coherence`
with an explicit construction of the comparison isomorphisms and a reduction of their
compatibility to one categorical counit equation. The target signature is unchanged.

The private proofs `flat_retract` and `transported_model_flat` prove that transporting
the strictly perfect complex through the open-site equivalence gives a bounded-above
flat complex. `pinned_counit_isIso` applies `flatComplexDerivedPullback` and the
left-derived universal property to prove invertibility of the particular counit
pinned by `exists_derivedPullbackComposition`. `open_model_iso` constructs the
representing isomorphism on the open subscheme using the existing
`singleComplexOpenPullbackIso` and exact-functor comparison isomorphisms.

For each factorization, the proof composes the inverse derived composition comparison,
derived pullback of this fixed representing isomorphism, and the pinned counit
isomorphism. It applies `picard_termwise_composite_counit` to the hom of the fixed
representing isomorphism to prove the required compatibility.

The new module `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounit` states the
remaining equation for explicitly constructed morphisms. It allows arbitrary complexes
and arbitrary morphisms from the restricted derived object; it has no perfectness,
representation, or invertibility hypothesis. It asserts neither existence of comparison
isomorphisms nor coherence of arbitrary chosen families. Its source and full calculation
are in its docstring and node. No existing definitions or public signatures changed. The private `targetComplex`
definition caches the actual transported complex and contains no postponed data or proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_termwise_target_coherence`
(node `lem-sc-picard-termwise-target-coherence`) by reduction. Its module has no sorry.

Added one hole in
`AlgebraicGeometry.Scheme.picard_termwise_composite_counit`
(node `lem-sc-picard-termwise-composite-counit`). This is a decomposition, with one
hole closed and one added, hence net zero holes. The geometry, invertibility, actual
isomorphism construction, and combination are proved; the categorical compatibility
calculation remains. Every private helper is proved. Both delivered modules compile cleanly, and the
delivery axiom probes report no forbidden axioms or unexpected direct holes.

The remaining equation also holds for zero complexes and empty schemes: it uses only
naturality, the defining composition counit equation, and associativity, and never
cancels a possibly noninvertible counit or the arbitrary morphism e.

## No longer needed

Removed the proof import
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` and its direct proof
dependency `lem-pc-derived-pullback-open-restriction-universes`. The representing
isomorphism is now obtained from the already constructed exact-open comparison
`singleComplexOpenPullbackIso`, instead of the general two-open restriction theorem.
This is removal from this proof, not a claim that the module is globally unreachable.

The other original imports and dependencies remain needed. No unit statement or unit
proof step is bypassed; the cube unit and the original target-coherence route remain.

## Where the brief, the DAG or earlier work was wrong

The previous missing `PicardTermwiseModels.olean` blocker is resolved in the published
build; the original module now compiles against that build. The old sandbox contained
many compiled dependencies from earlier work. They were moved aside before checking
against the published baseline; the active overlay contains only this delivery's modules.

The saved report correctly rejected coherence of arbitrary comparison families. The
new equation is instead about the displayed composites of one fixed morphism with the
pinned counits. Their components are built explicitly and are never chosen from a
mere existence assertion.

Mathlib searches found the universal-property ingredients `leftDerived_fac_app` and
`isLeftDerivedFunctor_iff_isIso_leftDerivedLift`, but no complete Picard compatibility
equation. LeanSearch returned an Internal Server Error and is recorded as unavailable.

## New nodes

`lem-sc-picard-termwise-composite-counit`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-termwise-composite-counit.json`, states
the categorical equation for the displayed composites. Its one statement is in
`lean/Sheaf/AlgebraicGeometry/PicardTermwiseCompositeCounit.lean`. Its proof expands
the pinned left-derived composition equation through the complex/homotopy quotient,
then uses naturality and associativity. The original node's proof and proof dependencies
are updated to match the Lean reduction. The proof-environment change record is
`coord/changes/picard-termwise-target-proof-environment.md`; preflight conservatively
requires it for section-command changes. There are no forced adaptations.

## Second reading by E2

1. Compared the delivered target module with the repository version. The public theorem signature and existing declaration text are unchanged; only proof code, private helpers, section binder names/options, and proof-only imports changed. The new theorem is in a separate module and is recorded by its node. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py`; compilation succeeds. Sorries occur only in the named split theorem `picard_termwise_composite_counit`, with no sorry in definitions. No forbidden declarations were found. Scratch-copy `#print axioms` checks show that both declarations use only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` from the split and still-open upstream statements. Verdict: pass.

3. Checked the split statement against its use and the categorical calculation. It is strictly more general than the target reduction (arbitrary complex and arbitrary morphism `e`, with no perfectness or invertibility assumptions), and its conclusion is exactly the displayed composite equation. It does not restate the target theorem or duplicate an existing library declaration; searches found no duplicate. Verdict: pass.

4. Checked the proof from the target downward. The construction uses the existing strict-perfect model and open restriction comparison, then the shortest available universal-property route for the pinned counit. The removed open-restriction-universes import is unused, and the remaining imports support declarations actually referenced. The unit's cube route and all realized target-coherence steps remain represented. Verdict: pass.

5. Compared the target and split node records with the Lean declarations. Statements, proof dependencies, proof origins, source references, and the new module record agree; the target node records the split theorem as its sole additional dependency. Verdict: pass.

Changed during second reading: no Lean proof or statement changes were needed; this section was added to document the checks. Independent searches used `leftDerived.*comp|counit.*comp` and `CategoryTheory.Functor.leftDerived_ext`, and local searches examined the pinned composition/counit modules. The cube unit presently has empty `realized` arrays; this delivery does not alter them or bypass any unit step. The remaining quotient-level calculation is not a few-minute proof repair. The dry run passed with review class CODEX.
