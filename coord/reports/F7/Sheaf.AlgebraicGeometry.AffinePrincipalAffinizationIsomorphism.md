## What changed

Proved AlgebraicGeometry.affine_principal_affinization_isomorphism, with its existing
signature unchanged. Mathlib's qcqs section-localization isomorphism transports to
an isomorphism on global sections of the restricted morphism. The affine
spectrum/global-sections comparison then proves the scheme isomorphism. The ring
equivalence is constructed from the actual canonical awayToBasicOpen map, and its
fraction formula follows by multiplication and cancellation of the restricted unit.
Updated the theorem's proof explanation and the node's proof, proof_deps and
proof_origin to this route. No definitions, statements or other modules changed.

Validation: remote lcompile.py passed in 11.3 seconds with no errors or warnings.
A temporary #print axioms check reported exactly propext, Classical.choice and
Quot.sound. Removed the diagnostic command afterward. The proof handles f=0,
nilpotent f, units, zero-divisors, n=0 and the empty scheme uniformly: cancellation
is only of the invertible restriction of f, including in the zero ring.

## Proved and sorry left

Closed 1 of 1 holes: AlgebraicGeometry.affine_principal_affinization_isomorphism
(lem-a1-affine-principal-affinization-isomorphism). No sorry remains. Added zero
holes and split off zero statements. This is a proof, not a decomposition.

## No longer needed

Removed private proof imports Mathlib.AlgebraicGeometry.ResidueField,
Mathlib.AlgebraicGeometry.Morphisms.IsIso,
WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization,
WeilConjectures.AlgebraicGeometry.Modules.Invertible, and
Sheaf.AlgebraicGeometry.CoherentFiniteType.

This proof no longer needs lem-sc-p1-invertible-section-localization,
def-sc-invertible-module, or pqf-def-coherent. Mathlib already proves precisely
the qcqs structure-sheaf localization input; constructing tensor powers and a
Laurent presentation adds no needed result here. Removed the obsolete top-level
tool_uses approval for lem-sc-p1-invertible-section-localization. No modules are
withdrawn, and no claim is made that other consumers do not need those modules.
The affine-open localization node, affine-section isomorphism criterion,
affinization node and ring-localization node remain in the proof route. Public
imports are unchanged. The unit's statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly found the Mathlib qcqs section isomorphism but the
planned proof still reconstructed it via invertible-module localization.
The section isomorphism suffices directly once transported through appLE and
resLE_app_top. This avoids all tensor-power and Laurent-localization glue.
The original theorem statement is correct; no repair to its meaning was needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
