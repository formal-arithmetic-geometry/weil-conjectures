## What changed

Proved the four theorem holes in `Sheaf.Paper.RHomColimitCohomologyLadder`, preserving all public statements and definitions. The proof uses adopted exact-colimit homology, the existing canonical source-transport interface, and the proved signed contravariant exactness interface. Private helpers construct the canonical cohomology comparison, transport the three rotated exact spots, preserve exact diagram rows under filtered colimits, and prove the vertical naturality square.

## Proved and sorry left

Closed four holes: `WeilConjectures.SfbHomFilteredColimit.ladder_filtered_cohomology`, `WeilConjectures.SfbHomFilteredColimit.ladder_filtered_consequences`, `WeilConjectures.SfbHomFilteredColimit.ladder_comparison`, and `WeilConjectures.SfbHomFilteredColimit.rhom_colimit_cohomology_ladder` (node `lem-sfb-rhom-colimit-cohomology-ladder`). Added zero holes and zero split statements. No sorry remains in the delivered module. Existing imported theorem dependencies retain their own proof status.

## No longer needed

Removed the private imports `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`, `Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses`, `WeilConjectures.Algebra.Homology.HomComplex`, and `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`. Their remaining definitions and generic APIs are already available through the retained public imports and the signed exactness interface. No public import is changed.

The node no longer directly requires `lem-pur-ringed-site-grothendieck-abelian` (use its independent-universe Grothendieck category theorem), `def-pur-hom-complex` as a direct proof step (no component or differential calculation is needed), or `lem-pur-rhom-well-defined-universes` (source localization is supplied by the existing canonical source-transport interface), or `lem-weil-pbc-derived-cohomology-ladder` (each square follows directly from naturality and the colimit universal property). The strict Hom definitions remain available through the unchanged statement imports and are still used to form the model. Removed the three corresponding obsolete top-level `tool_uses` entries, preserving the remaining entries in order. These are direct-edge removals only; no globally unused module is claimed and no module is withdrawn. The unit route is preserved.

The proof-command change record is `coord/changes/rhom-colimit-cohomology-ladder-proof-commands.md`; the static checker requires it for the opposite-namespace opening and local irreducibility attribute. There are zero downstream Lean modules and no forced adaptations.

## Where the brief, the DAG or earlier work was wrong

The original shift dependency proves covariant exactness; the source ladder needs the subsequently proved `signedDerivedInternalHom_exact` theorem, including its degree -1 normalization. The adopted source already proves that complex homology preserves exact colimits, so the cycle-boundary argument need not be rebuilt. No mathematical statement was changed. The independent-universe Grothendieck theorem is used as generic ambient category infrastructure: the restricted-functors unit supplies no module-sheaf exact-colimit theorem. The signed exactness theorem supplies the needed source normalization; the original covariant exactness interface alone does not. Validation: the prescribed single-file server compiler compiled the complete module cleanly in 23.9 seconds, with no errors or warnings. The local irreducibility attribute on homComplexFunctor prevents its implementation from unfolding in the categorical identity calculation; no definition is changed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
