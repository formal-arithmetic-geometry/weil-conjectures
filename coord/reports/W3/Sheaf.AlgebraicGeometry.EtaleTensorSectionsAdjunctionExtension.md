## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsAdjunctionExtension`
without changing its signature or any of the seven existing public definition bodies.
The added helpers are private and proved. The construction of `b_u` is explicit:
its value on a section is the prescribed restriction of `beta`. Its module linearity
uses `extensionScalarSquare`, proved from `morphismRestrict_appTop` and naturality
of the scheme structure map. Its compatibility with restrictions uses
`morphismRestrict_homOfLE`.

For a triangle, `extensionTriangleMap` is the explicit map `G_u -> f_*G_v`.
Functoriality of G gives `extensionBaseMap_triangle`. The unit identity for conjugate
adjunctions then proves `extensionComp_homEquiv`, and injectivity of the adjunction
Hom equivalence proves compatibility of the transposed maps. Taking global sections
and checking the actual top-open transports gives the natural transformation.
Componentwise linearity follows by cancelling the ring map of the top-open isomorphism.
A private typed alias names the same prescribed adjunction, avoiding repeated elaboration
of its large section-normalization existence statement.

`extensionOpenUnit` proves the unit formula for the already constructed
`tensorOpenSectionIso` directly with `unit_leftAdjointUniq_hom_app`, naturality and
Mathlib's restriction-unit formula. It gives the prescribed open normalization.
Naturality in M and G follows from the two naturality equations for
`homEquiv.symm` and naturality of the presheaf module map k. No quasi-coherence,
nonemptiness, or finiteness is used; empty opens and zero modules obey the same
functorial and unit equations.

Updated the existing node's proof and proof dependencies to this argument. Removed
five unused public imports and added one private Mathlib proof import. The change
record is `coord/changes/W3-etale-tensor-extension-imports.md`. Only this item's
existing Lean module and node are changed; there are no new modules or nodes.
The original statement and definition bodies were also checked textually unchanged.

Searches: LeanFinder found individual pullback adjunctions but no extension theorem;
Loogle and the project Mathlib grep found the generic Hom-equivalence naturality
and left-adjoint unit identities used here. The source-library search found no
duplicate of the extension construction.

Validation: `lcompile.py --all` compiled the item in 57.4 seconds and both
unchanged direct importers: `EtaleExtensionFreePresentationsHom` in 31.3 seconds
and `SchemeEtaleRelativeDifferentialsComparison` in 20.4 seconds. The temporary
importer copies were removed after validation. Development profiling options were
removed before the required delivery compile and axiom checks.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsAdjunctionExtension`
(node `lem-trf-etale-tensor-sections-adjunction-extension`).

Holes closed: 1 of 1. Holes added: 0. Holes left in the delivered Lean file: 0.
No decomposition or split-off theorem is used.

## No longer needed

Removed these imports from the item:

- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
- `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`

The proof no longer uses node
`lem-weil-pbc-open-immersion-module-pullback-restriction`: the needed open-unit
calculation is proved directly from the generic left-adjoint comparison unit identity.
It no longer uses `lem-sc-etale-tensor-sections-map-naturality`: naturality in the
module variables is proved directly for the constructed components. These entries
are removed from proof dependencies and the latter obsolete tool-use approval is
removed. Historical statement dependencies are retained; this does not claim that
these nodes are globally unreachable.

The general module-sheaf notion still uses Mathlib's actual `PresheafOfModules`
and sheaf condition; the extra `ringedSiteModules` abbreviation is unnecessary.
The section-normalized pullback interface is unnecessary because the statement
already fixes the adjunction via `exists_tensorPullbackAdjunction`, which also
normalizes `tensorSectionsComp`. Sheafification is already part of the imported
explicit tensor construction and is not used as a separate step here.

No module is withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The proof plan was mathematically sound. The direct-image composition is implemented
by `pushforwardComp`, with identity maps on sections, rather than a literal equality
of functors. The node now records this identification explicitly.

The initially expensive open-unit rewrite tried to unfold the concrete tensor
construction. Keeping `tensorPullback` and `tensorPullbackObj` locally irreducible
and proving the unit calculation first for an arbitrary left adjoint avoids that
expansion. The tensor case is a direct specialization. Replacing inference of
the opens from their section types by the explicit `restrict_map` formula removes
the remaining elaboration hotspot. No shared
reducibility attribute, definition, instance or public signature was changed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
