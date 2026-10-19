## What changed

Closed both declarations in `Sheaf.Paper.BoundedFlatReplacement`.
The proof constructs a functorial free presheaf cover over the given constant ring sheaf,
sheafifies it, proves categorical flatness from sectionwise free modules and the
independent-universe tensor comparison, and applies the existing cycle-pullback
construction. It then proves termwise epimorphy by two compatible-pair refinements and
quasi-isomorphy with Mathlib's homology-map refinement criteria. The ZMod theorem is the
evaluation of the resulting functor and augmentation. The proof imports are private.

The change record `coord/changes/bounded-flat-replacement-proof-scopes.md` documents the
new section-local commands and private helpers requested by the preflight, including every
transitive consumer. Both public signatures and all public imports are unchanged; no
consumer adaptation is required.

The DAG node proof and proof dependencies were updated to this route. No statement was
changed. The old equal-universe sheafification-flatness wrapper is not used because the
small etale site and coefficient sheaf use distinct universes; the proof uses the
independent-universe tensor API directly.

## Proved and sorry left

Closed the two original declarations:

- `AlgebraicGeometry.Scheme.exists_functorial_bounded_flat_replacement`;
- `AlgebraicGeometry.Scheme.exists_bounded_flat_replacement_zmod`.

Holes closed: 2. Holes added: 0. No `sorry` remains in the item module.
This is a proof from existing named dependencies, not an assertion that their transitive
proofs are all closed. The retained proof was rechecked against current sources and
compiled cleanly through `lcompile.py` on 2026-10-19 (15.0 seconds in this resumed session).

## No longer needed

Removed the following original proof imports:

- `Mathlib.LinearAlgebra.FreeModule.Basic`;
- `Mathlib.RingTheory.Flat.Basic`;
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`;
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`;
- `Mathlib.CategoryTheory.Sites.Abelian`;
- `Mathlib.CategoryTheory.Sites.Sheafification`;
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`;
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`.

The free-module, flatness and sheafification APIs still enter through the narrower imports
actually used by this proof. The equal-universe flat-sheafification wrapper is unnecessary:
the proof constructs its comparison at independent universes directly.

Removed these original direct proof dependencies from the node:

- `def-weil-pbc-constant-sheaf`;
- `def-weil-pbc-sheafification`;
- `lem-pc-sites-modules-sheafification-flat`;
- `lem-weil-pbc-sheafification-sets-exact`;
- `lem-weil-pbc-site-module-presheaf-sheafification-exact`.

The constant coefficient sheaf remains in the statement; its definition is available through
the unchanged statement imports. The proof works over its ring sheaf directly and uses the
module-sheafification adjunction instead of transporting constant presheaf scalar actions.
It proves quasi-isomorphy after the cycle construction on sheaves, so it does not need
sectionwise presheaf homology or a homology/sheafification comparison. The obsolete
`tool_uses` approval for `lem-pc-sites-modules-sheafification-flat` is also removed.

The alternative generic module `Sheaf.Algebra.Homology.BoundedFlatReplacement`,
extension-by-zero flat covers and coproduct-flat modules are not imported. The proof uses
`Sheaf.Algebra.Homology.CyclePullbackResolution` and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`, together with Mathlib's
free presheaf and homology-refinement APIs. No unit-level route is bypassed. These are
local dependency removals; no claim is made that another target does not need those nodes.

The Mathlib and library searches found no shorter declaration of the functorial bounded
flat replacement. LeanFinder returned only general sheaf, free-resolution and left
resolution declarations; Loogle returned no hit; grep found only the generic
left-resolution documentation.

## Where the brief, the DAG or earlier work was wrong

The original imported blueprint proof uses a full next-term pullback; that does not force
square-zero differentials. The existing cycle-pullback dependency records the repaired
construction. The earlier equal-universe flat-cover wrapper cannot be instantiated at the
small etale universes in this target, so this proof constructs the same free cover locally
and uses the independent-universe sheaf tensor comparison. This is an interface limitation,
not a change to the target statement.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
