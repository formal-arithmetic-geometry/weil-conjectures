## What changed

Proved `CategoryTheory.ringFamilyGlobalExtension_quasiIso_of_kflat` with its signature
unchanged. Added only private proof imports and fully proved private helpers. The
sectionwise tensor/pullback adjunction formulas are reused from the existing private
construction in `GlobalSectionRingFamilyBaseChange`; they are included locally to avoid
importing its unrelated Cech-model theorems. No source-library module is changed.

At each site object, `ringComplexExtensionSections` identifies the sectionwise tensor
complex with the evaluated one-point scalar-extension complex. The existing
`SheafOfModules.changeOfRings_kFlat_quasiIso` proves the latter map is a quasi-isomorphism.
The comparison is checked on pure tensors for both differentials and the given map.
Objectwise detection, adjunction uniqueness, and exact sheafification finish the proof.
There is no flatness hypothesis on the evaluated coefficient ring. The empty site,
zero rings and zero complexes are covered by the same proof.

Validation: the remote single-file compile passed without diagnostics in 25.8 seconds,
within the 60-second limit. The delivery tool runs the required server preflight.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.ringFamilyGlobalExtension_quasiIso_of_kflat`
(node `lem-weil-pbc-global-section-scalar-kflat-quasi-iso`).

No sorry remains in the delivered module. Added 0 holes and split off 0 statements.
All private helpers have complete proofs. The proof uses existing named library results.

## No longer needed

No existing public import was removed. The original node's direct dependency
`lem-pc-kflat-resolution` is unnecessary: the existing proved
`lem-pur-change-of-rings-kflat-quasi-iso` already packages the resolution argument.
The resolution theorem remains needed inside that theorem; no module is withdrawn.
No new resolution, one-point tensor equivalence, Cech-model hypothesis, or derived-category
comparison is needed here. `Sheaf.Paper.GlobalSectionRingFamilyBaseChange` is not imported;
only the private tensor-presheaf formulas used by this proof are reused locally.

## Where the brief, the DAG or earlier work was wrong

The DAG's plan is mathematically sound, but resolving each O(X) again is unnecessary:
apply the existing change-of-rings theorem to the explicit one-point extension. Its
object and map identifications are definitional equalities. The remaining presheaf
comparison is substantive glue and is now fully proved. The unit route is unchanged;
no target statement, definition, or consumer interface is altered.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
