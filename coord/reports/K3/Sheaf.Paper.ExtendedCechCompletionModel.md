## What changed

Worked in `lean/Sheaf/Paper/ExtendedCechCompletionModel.lean`. Added compiled categorical helpers; the public-surface change is recorded in `coord/changes/extended-cech-completion-splits.md`. for naturality of the canonical completion unit, conversion from internal-Hom isomorphisms to bijectivity on morphisms, and the categorical unit-isomorphism argument. Split the unimplemented construction and reflector clauses into two named public theorems, then combined them in the original target with a real proof.

## Proved and sorry left

The original target `CategoryTheory.exists_ringedExtendedCech_completion_model` is reduced to the two strictly smaller named clauses and compiles. The following declarations remain sorry and are represented by new DAG nodes:

- `CategoryTheory.exists_ringedExtendedCech_global_model` (`lem-weil-pbc-extended-cech-global-model`)
- `CategoryTheory.ringedExtendedCech_reflector_properties` (`lem-weil-pbc-extended-cech-reflector-properties`)

No sorry occurs in a definition. The private categorical helpers are proved.

## No longer needed

No existing imports or proof-dependency nodes were removed. The proof uses the existing derived internal-Hom, completion-unit, ringed localization, local completeness, and global-sections interfaces. The special-cocontinuous site-equivalence and ring-complex functorial declarations remain needed by the split construction clause's documented route.

## Where the brief, the DAG or earlier work was wrong

The planned proof assumes a comparison between the sequential-colimit localization `ringedSiteSectionLocalization` and the fraction localization `ringedSectionLocalization` used by the explicit extended Cech complex. No such comparison theorem is exposed in the current library, so the construction and reflector arguments cannot be completed from the recorded interfaces in this session. The split isolates these two strictly smaller obligations.

## New nodes

- `lem-weil-pbc-extended-cech-global-model`: construction of the global augmented model.
- `lem-weil-pbc-extended-cech-reflector-properties`: completeness, naturality, universal mapping property, and complete-object unit isomorphism for a given model.

Change record: `coord/changes/extended-cech-completion-splits.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
