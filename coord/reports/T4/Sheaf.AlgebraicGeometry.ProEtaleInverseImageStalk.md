## What changed

Completed both declarations in `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`.
The proof constructs the pro-etale point represented by arrows from the geometric point,
identifies its category of elements with pointed weakly etale neighbourhoods, and applies
the existing generic site-point comparison and unit-germ formula. It specializes the result
to sets and additive commutative groups. The proof-only imports are now the direct point,
Elements, TypeValuedFlat, weakly-etale, and inverse-image comparison modules needed by
that construction.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.proEtaleInverseImage_setStalk` and
`AlgebraicGeometry.Scheme.proEtaleInverseImage_abelianStalk`. No `sorry` remains in the
item or is added by this delivery. Holes closed: 2; holes added: 0; split off: 0.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk`,
`Sheaf.Paper.SiteSheafificationSectionsLocal`, `Sheaf.RingTheory.IndPrincipalZariski`,
`Sheaf.RingTheory.WeaklyEtaleField`, `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
`Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, `Mathlib.FieldTheory.IsSepClosed`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`,
`Sheaf.RingTheory.IndEtaleUniverseTransport`, and
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`. The direct
`WeilConjectures.Mathlib.CategoryTheory.Elements` import supplies the Elements construction.
The proof no longer uses the planned
manual sheafification-local-sections, residue-field, or cocone route, nor the corresponding
DAG nodes `lem-galois-fpqc-covering-base-change`, `lem-weil-pbc-weakly-etale-composition-base-change`,
`lem-weil-pbc-weakly-etale-source-locality`, `def-weil-pbc-ind-etale-algebra`,
`lem-weil-pbc-weak-etale-field`, `lem-weil-pbc-separable-extension-embeds-separably-closed`,
`def-weil-pbc-sheafification`, `lem-weil-pbc-site-sheafification-sections-local`, and `lem-cbc-proetale-sheafification-geometric-stalk`.
The proof dependency list also drops `def-weil-geometric-point` and
`def-weil-affine-spectrum`: the geometric-point data remains in the unchanged statement,
while the direct argument needs no separate theorem about the residue-field description.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expanded the point and sheafification argument even though the library
already contains the generic site-point comparison with the exact germ equation. The
retained proof follows the shorter route through that established comparison and the
existing weakly-etale section theorem. The item statement and both theorem signatures are
unchanged.

The obsolete top-level tool approvals for the seven replaced planned tools are removed.
The unit `sk-prop-a1-inv` has no statement or proof-step realizations attached to this
item or the removed dependency nodes, so the change stays below the unit route.

Rechecked against the current shared sources on 2026-10-19: both theorem signatures
are identical, and the three subsequently added proof imports listed above are unused
by this route and removed as well. No consumers require adaptation.

Validation: the complete module compiled again through `lcompile.py` on 2026-10-19
in 5.7 seconds with no diagnostics. Both public signatures were compared verbatim
against the current shared module and are unchanged. All Lean lines are at most
100 characters. The DAG changes are limited to the proof route, its dependencies,
its source, and removal of obsolete top-level tool approvals. No consumers require
adaptation. The unit realization record remains unchanged.

Earlier delivery attempts were interrupted by compile-server and delivery-worktree
infrastructure failures; the completed proofs were retained. This resumed session
reruns the required dry run before delivery. Launcher scripts were not changed.

The first resumed dry run passed compilation and reached preflight. It requested
a change record solely because `universe u` becomes `universe u v w` for the private
generic helper. Added
`coord/changes/proetale-inverse-image-stalk-private-universes.md`, documenting the
old and new command and every transitive consumer. Module-local universe names do
not affect any importer; all existing public theorem signatures and public imports
are unchanged. No consumer source is modified.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
