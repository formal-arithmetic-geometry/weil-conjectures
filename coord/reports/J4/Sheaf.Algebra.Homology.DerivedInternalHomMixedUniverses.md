## What changed

Filled the invariance, functorial replacement comparison, and representative comparison
proofs of `Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses`. Added the proved
mixed-universe Hom-complex invariance companion in
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMapMixedUniverses`, imported privately.
The localization and canonical K-injective construction stay unchanged.

The new companion follows the existing sectionwise proof, with rings in `r` and module
sections in `max u v r`: product projections identify cochains and their differentials,
homology identifies naturally with shifted homotopy classes, exact slice restriction
preserves K-injectives, and Mathlib’s `Qh_map_bijective` transfers invertible
pre- and postcomposition from the derived category.
Exact sheafification then detects the module-sheaf quasi-isomorphism. Existing exact
extension-by-zero and restriction results are reused. All supporting helpers are private
and proved. The private comparison statements use equality of localized morphisms,
which avoids repeated unfolding of the scalar-restriction constructions.

## Proved and sorry left

Closed the three original holes, all attached to `def-pur-derived-internal-hom`:

- `CategoryTheory.derivedInternalHomMixedUniverses_inverts`.
- `CategoryTheory.derivedInternalHomMixedUniverses_comparison`.
- `CategoryTheory.derivedInternalHomMixedUniverses_obj_iso`.

Added zero holes. The new public theorem
`CategoryTheory.quasiIso_homComplex_mapMixedUniverses` is proved, with node
`lem-pur-rhom-well-defined-mixed-universes`. No `sorry` remains in the delivery.
The existing resolution-existence theorem is used as stated; its proof is outside this item.

## No longer needed

The new proofs do not use `lem-pur-rhom-well-defined-universes` or its module
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses` directly: that interface forces
the coefficient-ring universe to equal the section universe. The new proved companion
keeps the smaller ring universe. The old node remains needed for the re-exported
`derivedInternalHomOfUniverses` interface, so it is not withdrawn or globally pruned.
No existing public import is removed; both public imports retain interfaces used by
consumers. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG proof cited the common-universe Hom invariance theorem for a mixed-universe
construction. Its Lean signature does not accept the independently smaller ring sheaf.
The proof route is valid after supplying the proved mixed-universe companion; no statement,
definition, target, or unit route changes. The comparison is through the common target
`I(I₀(M))`, with both comparison maps proved quasi-isomorphisms by naturality and
two-out-of-three. Representative transport uses the contravariance in the first argument.

Edge cases retain arbitrary unbounded complexes, all integer degrees, zero modules, and
arbitrary topology. No boundedness, ring finiteness, or extra site hypothesis is introduced.
Slice sheafification instances use the existing essentially-small-site transport with their
universe fixed explicitly. All edits are in the assigned sandbox.

## New nodes

`lem-pur-rhom-well-defined-mixed-universes` records the proved independent-ring version of
Stacks 0A95. Its statement is a Hom-complex invariance result, strictly below the derived
bifunctor construction. Its proof uses the existing exact extension-by-zero and restriction
APIs and Mathlib's K-injective localization comparison. Blueprint and Mathlib searches
were run before recording it. No change record is needed: existing signatures, public
imports, definitions, and visibility are unchanged.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
