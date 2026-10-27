## What changed

Proved `CategoryTheory.ringedKoszulCompletionReflector` with its original signature.
The proof derives finite type from the specified slice generating lists, verifies
`HasLocalExtendedCechDescription` for the actual augmented Cech complex, applies
`ringedExtendedCech_reflector_properties`, and transfers its properties across
`exists_ringed_cech_koszul_comparison_on_site`.

The local description uses the existing global model and augmented restriction theorem.
An arrow isomorphism need not have the canonical ring component. A proved private
helper corrects this discrepancy: fully faithful degree-zero embedding lifts every
derived ring-complex automorphism to a chain automorphism, and conjugating its tensor
with the identity by the left unitor extends it across any augmentation. This gives
the required canonical ring comparison without changing the restriction theorem.
The inverse on Hom sets is explicitly the Cech extension preceded by theta inverse.
Completeness transports through restriction and derived internal Hom; the comparison
unit equation proves both the unit-isomorphism criterion and naturality.

Only this module and the existing node's proof fields change. The node currently
attaches a completed-coefficient specialization; its existing attachment and proof
steps are preserved, and separate steps record the general companion proved here.
No public imports, definitions, statements, or source-library modules change.
The construction works for an empty site, empty list, zero generators, units and
zero rings: finite type uses all objects as a cover, and scalar normalization uses
only isomorphisms and monoidal naturality, never nonvanishing or a chosen generator.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ringedKoszulCompletionReflector`
(node `lem-weil-pbc-ringed-koszul-completion-reflector`).
Zero holes remain in the delivered module; zero holes are added or split off.
The proof uses existing declarations with their existing admitted dependencies;
it does not claim those dependencies have been discharged.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`: its single-site comparison suffices;
  no slice tower presentations, uniqueness, colimit or coherence clauses are needed.
- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`: the existing general Cech
  reflector already gives completeness for every ideal section.
- `Sheaf.Paper.RingedLocalizationRHomCalculus`: no separate generator contraction or
  currying calculation is needed in this proof.
- `WeilConjectures.Algebra.Homology.DerivedInternalHom`: available through the unchanged
  public statement imports.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`: the single-site comparison
  already supplies the strict derived-limit presentation and prescribed unit.

Accordingly, the general companion does not directly need nodes
`lem-weil-pbc-ringed-cech-koszul-dual-limit`,
`lem-weil-pbc-ringed-derived-complete-elements-ideal`,
`lem-weil-pbc-ringed-localization-rhom-calculus`, or
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` as separate proof steps.
The single-site comparison retains its own strict-limit dependencies; no claim of
whole-project unreachability is made. The node's older specialization dependencies
remain because that separate declaration still uses them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node's current proof describes only `wfCompletionReflector`, while this assigned
module is its original general ringed-site companion. Appended the companion's actual
proof steps without removing the specialization's route or replacing its attachment.
The existing full Cech/Koszul comparison requires derived tower instances on every
slice beyond this theorem's hypotheses; the single-site comparison has exactly the
needed hypotheses and avoids introducing those assumptions.
The augmented restriction theorem specifies an arbitrary ring arrow component;
treating it as the canonical component would leave a gap. Scalar normalization
closes that gap inside the proof.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
