## What changed

Proved CategoryTheory.ringedInternalHom_covariant_exact from the existing native derived
tensor-Hom adjunction and Mathlib's triangulated right-adjoint theorem. The native derived
tensor commutes with shifts and is triangulated. Its right adjoint inherits a coherent shift
structure and triangulatedness. The recorded independent-universe Hom specializes
definitionally to derivedInternalHom on this small site, with the localization universe
still arbitrary. All theorem binders, universes, visibility, and public imports are unchanged.

Validation: the delivered module compiled in 36.9 seconds without warnings.

Only the assigned module and its proof route in the DAG change. No definition changes,
consumer adaptations, new modules, or new nodes are required.

## Proved and sorry left

Closed CategoryTheory.ringedInternalHom_covariant_exact: one of one original holes.
Added holes: zero. Sorry left in the delivered module: zero. No statements are split off.

## No longer needed

The assigned proof does not use its old separate cone-construction route:
lem-pur-homotopy-category-triangulated, lem-weil-pbc-hom-into-triangle-exact,
lem-weil-pbc-kinjective-shift, def-pur-kinjective-complex,
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-kinjective-hom-derived,
def-weil-triangulated-category, lem-sf-triangle-morphism-iso,
lem-sc-hom-complex-mapping-cone, def-pur-hom-complex, def-pur-derived-internal-hom.
Some remain transitive prerequisites of the reused adjunction; no global pruning or
withdrawal is claimed. The assigned module adds only private proof imports for the native
adjunction, generic triangulated adjunction API, and explicit small-site sheafification.

## Where the brief, the DAG or earlier work was wrong

The cone proof was a valid plan, but the existing native tensor-Hom adjunction already
supplies the shorter route at arbitrary derived-category universe. The theorem asks for
existence of a coherent shift structure, so the structure induced by this adjunction is
sufficient. The adopted derived tensor theorem includes arbitrary unbounded objects;
no K-flatness, boundedness, or coefficient hypotheses are imposed on L. The sheaf category's
functorial flat resolutions supply the tensor construction. Zero objects, identity and zero
maps, and negative shifts are covered by the generic adjunction and CommShift laws.

The proper-base-change unit and each of its realized steps remain unchanged.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
