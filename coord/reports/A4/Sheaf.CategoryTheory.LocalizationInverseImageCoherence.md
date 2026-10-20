## What changed

Completed both comparison proofs in
`lean/Sheaf/CategoryTheory/LocalizationInverseImageCoherence.lean`.
All existing public signatures, universes, visibility, public imports and definition
bodies are unchanged. Added only proved private helpers and proof-only imports.

The module localization is the sequential colimit of multiplication by the scalar.
The regular-module localization colimit comes from the existing declared algebra lemma;
tensoring and module sheafification give the actual tensor-defined localization and its
specified unit. The underlying-set functor preserves these filtered colimits. The set
adjunction and the supplied underlying-set comparison therefore make the module inverse
image preserve them too. Comparing the normalized colimits proves existence, naturality
and uniqueness of the module comparison.

For rings, the finite-product comparison and the supplied graph equations transport
ring morphisms directly. Applied to the localization unit, they give a ring morphism
from S to the inverse image of R[1/t], inverting s. The objectwise localization universal
property and sheafification give a ring extension from S[1/s]. Its underlying map respects
every sequential-colimit leg: the zero leg is normalization, and the successor step
cancels the invertible scalar. Thus its underlying map is an isomorphism, and forgetting
ring structure reflects isomorphisms. The inverse extension is the required comparison;
the ring localization universal property proves uniqueness.

The existing DAG node records this route and the two additional existing dependencies:
`lem-sc-module-localization-filtered-colimit` and
`lem-weil-pbc-module-sheaves-colimits-forgetful`. The former is a general algebra lemma,
not a use of the Picard unit's geometric argument. No unit realization is bypassed.
The new colimit structures have explicit components, and the component proofs avoid
expensive automated extensionality and unnecessary isomorphism instance searches.

Change record: `coord/changes/A4-localization-inverse-image-colimit-proofs.md`.
No other module or consumer needed adaptation. The full module compiled with both
comparison proofs and no remaining holes (33.8 seconds); the required delivery dry run
checks the final packet, including the line-length cleanup.

## Proved and sorry left

Closed 2 of the 2 original holes:

- `CategoryTheory.existsUnique_localizationInverseImage`.
- `CategoryTheory.existsUnique_localizationInverseImageRing`.

No `sorry` remains in the item. No holes or public intermediate statements were added;
no result was split off. Every private helper is proved.
The proof uses the existing declared theorem `ModuleCat.localization_away_colimit`
(node `lem-sc-module-localization-filtered-colimit`), whose own unfinished proof belongs
to that existing item. This delivery does not modify that theorem or move a hole into it.

The private constructions require no nonzero-ring, nonnilpotence, nonempty-site or
point-existence hypothesis. The colimit shift and cancellation arguments also apply to
nilpotent scalars and zero localizations. The ring inverse is constructed as a compatible
family by uniqueness of inverses, including in the zero ring.

## No longer needed

The following planned proof dependencies are removed from this node:

- `lem-weil-pbc-geometric-module-transport`
  (`Sheaf.CategoryTheory.GeometricModuleTransport`): module inverse image preserves the
  relevant colimits by its underlying-set comparison; a full module adjunction is unnecessary.
- `lem-weil-pbc-adjunction-lifts-group-ring-objects`
  (`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`): the ring map is transported
  directly from the graph equations, and the ring isomorphism is checked on the colimit.
- `lem-weil-pbc-sheaf-algebraic-structures-objects`
  (`Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`): no reconstruction of ring
  sheaves as internal ring objects is needed for this argument.
- `lem-weil-pbc-localization-tensor`: the regular-module colimit followed by tensoring
  gives the localization model without the separate localization/tensor equivalence.

These are removed dependencies of this node, not module withdrawals. Other users of
these declarations remain intact. Every original import is retained; the unused draft
import `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` was omitted. The existing
sheafification/tensor tool remains needed for the unchanged exactness argument.

## Where the brief, the DAG or earlier work was wrong

No existing statement or definition was found false. The module and ring-object
adjunction constructions in the original plan are longer than necessary for these
specific comparison assertions. The colimit route works directly with the existing
independent site universes and the specified algebraic inverse-image presentation.

Searches for inverse-image/localization comparisons found no directly applicable
Mathlib theorem. The declared sequential localization colimit and existing colimit
forgetful theorem provide the shorter route used here. The timeout during development
was resolved in the component proofs and cocone presentation, without changing the
compile limit, splitting the file, weakening a statement or adding an unfinished lemma.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
