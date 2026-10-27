## What changed

The item now assembles the first-residue isomorphism from ordinary coefficient squares,
exact localization, inverse mates of scalar adjunctions, and the index-zero common quotient
comparison of `integral_constant_completion`. The canonical integral realization, the given
normalized discrete residue isomorphism, and the literal `Q.objPreimage` in
`sfbResidueComplex` are retained. Existing public signatures, public imports and definition
bodies are unchanged. All added imports of the item are private proof imports.

`FixedScalarSmallCoordinates` proves the ordinary natural isomorphism between the prescribed
fixed-scalar model and normalized small-site scalar restriction. Identity maps on sections
lift through the fully faithful constant-scalar restriction.

`IntegralConstantSectionProjection` constructs uniquely normalized ordinary integer and
first-residue ring comparisons, their naturality square and every finite projection equation. It uses the existing `integral_section_projection_normalization`, naturality
of the canonical constant-section map, and the projection equations of the two completion
comparisons. The point topology comparison and the lifted quotient representatives are
identified explicitly. The two ordinary ring isomorphisms are packaged in a structure;
sheafification proves uniqueness, so their selection is determined by the normalization.
This helper involves no module, derived category or input complex.

Local irreducibility annotations prevent repeated unfolding of the section reconstructions
and scalar functors; explicit universe instances avoid ambiguous sheafification instances.
The standard derived-category construction and discrete model functors are locally irreducible.
The ordinary and derived restriction squares have explicit types, and additivity uses
binary-product preservation. Derived scalar extension is locally irreducible, including its
underlying universally specified choice data.
These changes reduce repeated reconstruction while checking the final derived isomorphism.
No existing definition or interface is repaired, and no consumer adaptation is included.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_residue_model_comparison`
(node `lem-sfb-integral-residue-model-comparison`).

Both added public helper theorems are proved:
`AlgebraicGeometry.Scheme.fixed_scalar_small_coordinates` and
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_constant_section_projection`.
There are zero `sorry` declarations in the three delivered Lean modules, zero holes added,
and zero split-off obligations. Existing admitted dependency declarations remain separate
stage-3 items; this delivery proves the item from their stated interfaces.

All three modules compiled together in import order with module outputs, within the
project compiler limit. The delivery tool performs final packet validation; its sole
style warning about an empty line in the ordinary normalization proof has been corrected.

## No longer needed

The planned direct uses of `lem-pe-internal-section-tensor-comparison` and
`lem-sfb-constant-scalar-restriction-tensor` are replaced by the proved inverse-mate theorem
`CategoryTheory.isIso_inverseMate_of_equivalences` and the exact restriction squares.
The elementary quotient calculation uses the representative equation of
`integralCoefficientULift`, rather than a direct appeal to the planned
`def-weil-l-adic-coefficient-extension` node. The unit's common-quotient route is retained.

The item no longer imports the private implementation of `IntegralModelsFlatResidue`;
it uses the uniquely normalized ordinary comparison structure instead. That dependency
remains in the proof of `IntegralConstantSectionProjection`. The duplicate private import
of `DiscreteCoefficientModel` is also removed: restriction along a ring isomorphism is
proved locally from the sectionwise inverse maps. Public local universe instances in the
ordinary comparison module keep its new definition signatures free of private helpers.
No original public imports are removed and no module is withdrawn. Existing source declarations
and their transitive imports remain; the unused planned proof nodes above are not claims that
their modules have disappeared from the library's import closure. No global module pruning
is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan did not state the ordinary normalization relating `completedSectionIso` to the
discrete-to-continuous scalar map. An arbitrary isomorphism from continuous coefficients to the
constant quotient limit would not identify the prescribed canonical realization. The proved
ordinary projection identity supplies this compatibility using the existing normalized
integral section projection theorem and the completion projection equations. No statement
was found false and no existing statement was weakened.

## New nodes

`lem-sfb-fixed-scalar-small-coordinates` records the proved ordinary fixed-scalar coordinate
comparison in `Sheaf.AlgebraicGeometry.FixedScalarSmallCoordinates`.

`lem-sfb-integral-constant-section-projection` records the proved ordinary coefficient
normalization in `Sheaf.AlgebraicGeometry.IntegralConstantSectionProjection`.

Both nodes belong to the original chapter and unit. The item node's proof and dependencies
now describe the inverse-mate assembly. There are no change records because no existing
statement, definition or public interface is changed.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
