## What changed

Completed AlgebraicGeometry.qcqs_relative_affinization_map in
Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap, with its exact statement preserved.
The unit-module instance and qcqs pushforward theorem prove quasi-coherence. The existing
affine_morphism_relative_spec equivalence supplies Y, π, a, and the affine charts.
affine_algebra_local_maps applied to a.inv supplies compatible local maps. Glue them on
the inverse images of all affine base opens, and use cover uniqueness to prove c ≫ π = f.
Cancel the top-section isomorphism in their section formula to recover c.appLE = a.inv_U.
Naturality of toSpecΓ on opens and a.hom_inv_id prove the chart equation.

Made AffineMorphismRelativeSpec a private proof import and publicly imported Mathlib
Morphisms.Affine and ModuleCat.Sheaf.Quasicoherent for the public statement predicates.
Removed unused imports CoherentFiniteType (public) and
Mathlib.AlgebraicGeometry.Modules.Tilde (private); added the private proof import
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent for its proved
isQuasicoherent_unit instance. The node proof now records this direct shortcut and the
actual section calculation. Change record:
coord/changes/F6-qcqs-relative-affinization-import-pruning.md.

Searches through the required msearch leanfinder, loogle and grep services found absolute
Gamma--Spec naturality but no complete relative-affinization result; local source search
found the existing affine-algebra gluing argument and the proved unit-module instance.
The proof follows Stacks constructions.tex, lemma-canonical-morphism (Tag 01LY), using
Tag 01LX for the relative-spectrum realization. No source-library declaration is changed.

## Proved and sorry left

Closed the one original hole, AlgebraicGeometry.qcqs_relative_affinization_map
(node lem-trf-qcqs-relative-affinization-map). Zero holes remain in the item module;
zero holes were added and zero statements were split off. This is a completed proof,
not a decomposition. No new declarations are introduced. The final module compiles
cleanly through lcompile.py (11.9 seconds); the exact theorem signature is preserved
verbatim, and every Lean line is within 100 characters.

## No longer needed

Removed the private import Mathlib.AlgebraicGeometry.Modules.Tilde and the public import
Sheaf.AlgebraicGeometry.CoherentFiniteType. Its extra finite-type predicate plays no role
in the statement or proof, which uses the existing IsQuasicoherent predicate directly.
AffineMorphismRelativeSpec remains needed, now only as a private proof import.
The unit-module quasi-coherence instance eliminates the planned proof dependency
lem-weil-pbc-spec-tilde-free-module; it is removed from this node's proof steps and
proof_deps. All other mathematical steps and dependencies remain. No module is withdrawn,
and no assertion is made that these modules are unused elsewhere in the library.

## Where the brief, the DAG or earlier work was wrong

The planned rank-one tilde argument is unnecessary: the adopted library already proves
quasi-coherence of the unit module directly. The relative-spectrum theorem packages its
existence clause through an equivalence; the proof extracts the inverse object and its
counit algebra isomorphism without restating any lemma. No mathematical statement needed
repair. Neither X_U nor affine-open intersections are assumed affine. The same cover
and categorical identities include empty bases and empty inverse images. The unit route
is preserved. There is no current return or rework row for this item.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
