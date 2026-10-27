## What changed

Reduced `WeilConjectures.GeneratorReduction.constantOpenAdjunction_nonempty` to the
ordinary inverse-image identity
`AlgebraicGeometry.Scheme.sfCbcOpenRestrictionModelComparison` in the new module
`Sheaf.SixFunctors.ConstantOpenRestrictionModelComparison`.

The original module now proves that its specified constant-module-to-slice transport
is an equivalence. It composes this equivalence, the inverse source model equivalence,
the existing literal localized module adjunction, and the target model equivalence.
The new comparison identifies the composed right adjoint with the fixed `modulePull`;
the unit/counit isomorphisms of the equivalences perform both cancellations. Finally
`Adjunction.ofNatIsoRight` supplies exactly the original adjunction statement.
No existing public signature, definition body, public import, target or unit route changed.

The two additional imports are proof imports: `import all
Sheaf.Paper.SfCbcExtensionZeroCompletion` exposes its proved private ringed transport
helpers, and the new comparison module supplies the remaining inverse-image identity.
The existing docstrings and all other proofs are preserved.

Validation: both modules compiled together. A subsequent profiled compile of the
item passed in 45.3 seconds; the profiling options were then removed. The delivery
command compiles the final files with the required declaration/axiom probes.

## Proved and sorry left

This is a decomposition, not a net hole closure: one original hole is closed and one
strictly smaller ordinary comparison hole is added. Zero of the original twelve holes
are claimed as independently proved; one is reduced. The adjunction composition and
both equivalence cancellations are complete Lean proofs. There is no `sorry` in a
private declaration or in a definition.

Closed by reduction:
`WeilConjectures.GeneratorReduction.constantOpenAdjunction_nonempty`
(node `lem-sf-constant-semilinear-generator-comparison`).

The eleven untouched holes in the item module all belong to
`lem-sf-constant-semilinear-generator-comparison`, with names in namespace
`WeilConjectures.GeneratorReduction`:

- `ordinaryRho_existsUnique`
- `rho_existsUnique`
- `ordinarySystemDirectIso_existsUnique`
- `ordinaryIntegralDirectIso_existsUnique`
- `systemDirectScalarIso_existsUnique`
- `ordinarySystemPullMap_isIso`
- `integralDirectScalarIso_existsUnique`
- `systemOpenScalarMap_isIso`
- `ordinaryIntegralPullMap_isIso`
- `integralOpenScalarMap_isIso`
- `constantSemilinearGeneratorComparison`

Added hole:
`AlgebraicGeometry.Scheme.sfCbcOpenRestrictionModelComparison`
(node `lem-sf-constant-open-restriction-model-comparison`). Its entire proof is
`by sorry`, with the source, full proof in words and empty-open/zero-ring checks
recorded in its docstring and node. It compares inverse-image functors only, for any
commutative ring, without mentioning an extension functor or an adjunction for it.

## No longer needed

None. No imports, declarations or nodes were removed. The other eleven obligations
remain unchanged, so no dependency of their planned arguments is declared pruned.
The new comparison becomes the next ordinary open-localization item.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. Step 11 had left the identification of the independently
specified module pullback with literal slice restriction implicit. This delivery
isolates that geometric comparison and proves the ensuing categorical argument.

`proEtale_ringed_open_comparison` was read: it supplies an equivalence for modules over
the actual inverse-image ring, but does not identify its existential equivalence with
`sfCbcConstantModuleToSlice` or compare the fixed `sfCbcMorphism.modulePull` on the
published model. Likewise `proEtaleOpen_slicePresentation` supplies an existential
slice presentation of the actual extension, rather than the required fixed functors.
Thus neither declaration directly closes this obligation. They are tools for the
remaining comparison, not replacement definitions of the functors. The new node names
the ringed-open comparison as a generic localization tool; the existing parent route
and its approved tools are otherwise preserved.

The Mathlib searches found Zariski structure-sheaf restriction adjunctions and the
standard categorical adjunction-transport lemmas, but no comparison of the specified
pro-etale constant-module model functors. The new node records all searches.

## New nodes

`lem-sf-constant-open-restriction-model-comparison`, in
`dag/nodes/sec-six-functors/lem-sf-constant-open-restriction-model-comparison.json`,
is the ordinary constant module inverse-image/slice restriction identity from Step 11.
Its new module is `Sheaf.SixFunctors.ConstantOpenRestrictionModelComparison`.
It introduces no data definition and no chosen adjunction. The parent node's Step 11,
proof dependencies and proof origin now record the proved equivalence/adjunction
composition and this remaining comparison. No change record is needed: existing
public declarations and definitions retain their original interfaces and meanings.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
