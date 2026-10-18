## What changed

Completed all five proofs in `Sheaf.Paper.RingedSiteIdeal`: restriction identity and composition,
ideal-module sheaf gluing, inclusion naturality, and unique extension of ideals. The extension is
constructed as the local saturation of the image-generated ideals using Mathlib's subfunctor
sheafification. Removed unused public imports of `Mathlib.CategoryTheory.Sites.Over`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, and
`Mathlib.Algebra.Category.Grp.FilteredColimits`.
The import-interface record is `coord/changes/ringed-site-ideal-imports.md`.

Validation: the completed module and both unchanged direct consumers
`Sheaf.Paper.RestrictionLocalCompleteness` and
`Sheaf.Paper.FlatRingedIdealCompleteEquivalence` compiled through `lcompile.py --all`.
All original declaration signatures and definitions are unchanged.

## Proved and sorry left

Closed 5 of 5 sorries, all under `CategoryTheory.RingedSiteIdeal` and all attached to
`def-weil-pbc-ringed-site-ideal`: `restrictionMap_id`, `restrictionMap_comp`,
`modulePresheaf_isSheaf`, `inclusionApp_naturality`, and `existsUnique_extension`.
Zero holes remain; zero holes added; zero split-offs.

The sheaf proof applies `Subfunctor.isSheaf_iff` to the actual ideal sections and `local_mem`.
The extension proof first proves restriction stability of image-generated ideals using
naturality and `Ideal.span_le`. Its local saturation is closed under addition by intersection
of covering sieves, and under multiplication on the same covering sieve. Mathlib's
`Subfunctor.sheafify_isSheaf` supplies local membership. The defining membership equivalence
and equality of section ideals prove uniqueness by proof irrelevance.

The construction permits empty covering sieves and zero rings without extra assumptions:
covering and saturation are handled by the Grothendieck topology API.

## No longer needed

The three removed imports listed above are not needed by the completed proofs. No DAG nodes or
modules are bypassed; the proof uses the existing ring-sheaf and subfunctor sheaf machinery.

## Where the brief, the DAG or earlier work was wrong

Nothing found.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
