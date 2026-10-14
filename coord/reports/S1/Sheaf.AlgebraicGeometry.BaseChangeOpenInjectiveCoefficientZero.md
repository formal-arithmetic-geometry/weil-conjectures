## What changed

Proved `AlgebraicGeometry.Etale.baseChange_open_injective_coefficient_eq_zero` with
its original statement. The proof constructs the coefficient map adjoint to the
injection into `Injective.under`, uses positive-degree vanishing on that injective
coefficient, and cancels the open Leray edge monomorphism on the geometric fiber.

Added `BaseChangeTargetCoefficientNaturality`, proving coefficient naturality of
the canonical target transition, and `EtaleOpenInjectiveLerayEdge`, proving the
edge monomorphism from the lower-degree comparison. The latter proof uses a cone
triangle and the long exact homology sequence, rather than constructing a spectral
sequence. No existing source-library definition or statement is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.baseChange_open_injective_coefficient_eq_zero`.
Proved the new declarations
`AlgebraicGeometry.Etale.target_transition_naturality` and
`AlgebraicGeometry.Etale.baseChangeTargetTransition_counit_mono`.

One new hole remains:
`AlgebraicGeometry.Etale.open_injective_coefficient_lower_comparison`, node
`lem-sbc-open-injective-coefficient-lower-comparison`. Thus the delivery is a
decomposition: one upper hole closed and one strictly lower hole added.

The remaining theorem needs the explicit identification of the unit/pullback/counit
composite with the derived base-change morphism on an injective single complex.
The canonical single-complex unit is invertible, and the derived counit agrees with
the ordinary counit after the single comparison. Combining these with the mate
formula proves the identification. Experiments proved these individual identities,
but the final formula still caused excessive equality unfolding. The delivered
named statement has the complete argument in its docstring.

## No longer needed

Removed the unused `LongExactSequence` proof import from
`EtaleOpenInjectiveLerayEdge`; the target module still uses that module's
positive-degree injective vanishing theorem. The dependency `sbc-lem-bc-injectivity` is unnecessary for this module: the
proved library injective-vanishing theorem supplies the first step directly, so
its parent proof dependency is replaced by `lemma-weil-pbc-leray-acyclicity`.
This does not claim that the critical-map node is globally unreachable; other
parts of the blueprint may still use it. The spectral-sequence construction in
the old plan is unnecessary; the cone argument proves the same edge monomorphism.

## Where the brief, the DAG or earlier work was wrong

The original plan's relative Leray edge and coefficient-coherence steps had no
usable Lean declarations. They are now explicit proved nodes. The parent node's
proof and proof dependencies have been updated to the route used by the code.
The target statement and all existing definitions remain unchanged. No statement
was disputed and no forced adaptation was needed.

## New nodes

`lem-sbc-target-transition-coefficient-naturality` records the proved naturality
square for arbitrary coefficient maps and integer degrees.

`lem-sbc-open-injective-leray-edge` records the proved degree-q monomorphism from
lower-degree base change. Its private generic cone argument is fully proved.

`lem-sbc-open-injective-coefficient-lower-comparison` records the remaining
comparison on injective coefficients, for every integer degree. Its hypotheses
are precisely those needed by the edge proof. Negative degrees, zero coefficients,
and the empty open immersion satisfy the same argument.

## Second reading by S1

1. I compared every delivered Lean module with the repository version. The existing target declaration has the same signature byte for byte; the added modules and existing node updates are recorded above. No definition or target statement was changed.

2. I compiled all four sandbox modules with `lcompile.py --all`; they compile without errors or warnings. The only remaining `sorry` is the named theorem `AlgebraicGeometry.Etale.open_injective_coefficient_lower_comparison`, and it has the matching split node and a complete proof plan in its docstring. No definition contains `sorry`, and no forbidden declaration was added.

3. I searched the library and Mathlib for the three added results and found no existing declaration duplicating them. The lower comparison is a genuine intermediate derived-category statement, strictly weaker than the target, and is required by the Leray-edge proof. Its edge cases are covered by its quantification over all integer degrees and arbitrary injective coefficients.

4. The proof follows the shortest available route: injective positive-degree vanishing, the cone/long-exact-sequence edge argument, and coefficient naturality. The unused long-exact-sequence import and the obsolete critical-map dependency were removed from the route where applicable; the unit route and `realized` nodes remain intact.

5. The DAG proof steps and `proof_deps` match the imports and theorem applications in the delivered code. The split node contains the required source, proof description, Lean declaration, and blueprint linkage.

I changed only this report section during second reading; no Lean proof or statement required repair.
