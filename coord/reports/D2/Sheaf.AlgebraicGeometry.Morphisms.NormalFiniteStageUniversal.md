## What changed

Proved `AlgebraicGeometry.Scheme.exists_normal_finite_stage_universal` with its original
signature and docstring. The construction is the concrete absolute normalization of the
scheme-theoretic image of the projection. Private helpers prove integrality of that image
and finiteness of its normalization over the integers, using
`RingTheory.finiteTypeZDomain_integralClosure_finite`.

Added the proved module `Sheaf.AlgebraicGeometry.Morphisms.NormalizationDominantLift`.
Its public theorem `AlgebraicGeometry.Scheme.existsUnique_lift_normalization_of_dominant`
constructs the dominant lift via generic points, relative normalization, and a pullback.
Uniqueness follows from the existing generic-field isomorphism and separated-target rigidity.
The main theorem uses this result for S and Y, and proves image factorization and both
compatibility equations in Lean. New proof imports are private imports.

Updated the item's proof, proof dependencies, and proof origin. Recorded the general
lifting theorem and attached the already proved source-library generic-field theorem.
No existing statement, definition, public import, or visibility was changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_normal_finite_stage_universal`
(node `lem-sbc-normal-finite-stage-universal`).

Added zero holes. Both delivered modules contain no `sorry`. The new public theorem
`AlgebraicGeometry.Scheme.existsUnique_lift_normalization_of_dominant`
(node `lem-sbc-normalization-dominant-lift`) is proved; it is not a split-off obligation.
The existing theorem `AlgebraicGeometry.Scheme.exists_iso_toNormalization_normalizationIn`
is attached at `lem-sbc-normalization-generic-field` without changing its module.

Both delivered modules compile cleanly through lcompile.py. The new lifting theorem's
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The original theorem
still transitively depends on `sorryAx` in the compiled existing finiteness dependency;
this delivery introduces no such dependency beyond the already imported ring-theoretic
finiteness module. This is a proof from the existing library declarations, not a claim
that the entire target import closure is now free of holes.

Edge cases: no compactness or finite-type condition on Y is used; empty affine opens are
handled by `isFinite_fromNormalization_of_finite`; integral schemes are nonempty, so
spectra of their function fields have exactly one point. The lifting theorem accepts
arbitrary integral normal sources and integral targets, including dimension zero.
Any other morphism in the main universal property is dominant because its composite
with beta equals the dominant alpha, so the uniqueness theorem applies to all candidates.

## No longer needed

None. No original import or proof dependency was removed. In particular
`Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite` and node
`lem-weil-pbc-finite-type-z-domain-normalization-finite` remain necessary for chart finiteness.
The unit's limit-reduction route is kept: this proves its single-stage image normalization,
without replacing the surrounding normal-stage diagram or Noetherian approximation.

## Where the brief, the DAG or earlier work was wrong

The proof plan was mathematically correct. The general absolute-normalization lifting
interface was missing; the new proved module supplies it. The source library already
contained the generic-field isomorphism used for uniqueness, but no DAG node recorded it.
LeanSearch returned Internal Server Error on both new-node queries; this is recorded as
unavailable, not as evidence of no match. LeanFinder and source grep were run and the
existing relative-normalization APIs were used.

## New nodes

`lem-sbc-normalization-dominant-lift`: the proved, general unique dominant lift through
absolute normalization. It is strictly a part of the original argument, has no approximation
system or finiteness conclusion, and is used twice in the main proof.

`lem-sbc-normalization-generic-field`: attaches the existing proved theorem
`AlgebraicGeometry.Scheme.exists_iso_toNormalization_normalizationIn` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`. It creates no Lean declaration
or proof obligation. Its specialization to the trivial function-field extension identifies
the generic point of absolute normalization for the uniqueness argument.

No change record is needed: all existing interfaces stay identical and the additional
module is imported only for proofs.

## Second reading by D2

1. **Unchanged statements.** Compared the delivered item module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports were added.

2. **Proof validity.** Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. Searched the delivered sources for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and `debug.skipKernelTC`; none occur. The proof uses only the existing normalization and dominance interfaces and introduces no hollow definition.

3. **New statements.** Checked `existsUnique_lift_normalization_of_dominant` against its node: it states exactly the dominant lift through absolute normalization, with no extra finiteness hypotheses. The generic-field node records an existing proved source theorem and adds no Lean obligation. The lifting theorem is a strict intermediate result used twice by the target proof.

4. **Pruning and route.** The target's proof dependencies and imports agree with the declarations actually used. No original import or proof dependency can be removed. The unit's single-stage image-normalization route is retained; the proof does not bypass the unit's route.

5. **Nodes and records.** The target and new nodes record the delivered declarations, statements, proof dependencies, origins, and source locations. The report's proved/sorry accounting closes the target hole and adds no holes. The unit record is unchanged because this delivery realizes the existing single-stage step.

Changed only the target proof, two proof-only imports, the proved lifting module, and the corresponding node records; no statement or definition was weakened or altered.
