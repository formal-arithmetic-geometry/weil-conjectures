## What changed

Proved both declarations in `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantHZero`.
The natural constant-section isomorphism is constructed from the sheafification unit at the
terminal étale object, with naturality supplied by `toSheafify_naturality`; its components are
isomorphisms by `Scheme.bijective_toSheafify_app_terminal` after proving the spectrum connected.
The degree-zero cohomology isomorphism uses the existing derived H-zero comparison and the
natural constant-section isomorphism.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.Etale.nonempty_strictlyHenselian_constant_sections_natural_iso`
- `AlgebraicGeometry.Etale.nonempty_constantSheaf_cohomology_zero_iso`

Added holes: zero. Sorries left in the delivery: zero.

## No longer needed

No imports or dependency nodes were removed. The proof follows the existing DAG route and uses
its connected-spectrum, constant-sheaf sections, sheafification, and degree-zero comparison
interfaces.

## Where the brief, the DAG or earlier work was wrong

Nothing was wrong with the statements or the planned route. The first theorem can be completed
 directly using the naturality equation for the sheafification unit and the existing bijectivity
 theorem for constant sections on connected schemes.

## New nodes

None.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
