## What changed

Proved `CategoryTheory.exists_ringed_cech_koszul_colimit_iso` without changing its
signature, universes, hypotheses, or visibility. Added the fully proved module
`Sheaf.CategoryTheory.RingedKoszulFactorColimit` and its public theorem
`CategoryTheory.exists_ringedKoszulFactor_colimit`.

The factor proof constructs the fraction maps a/s^(m+1), proves restriction and
transition compatibility, obtains the presheaf colimit sectionwise, and passes its
universal property through the module sheafification adjunction. Evaluation then
proves the two-term complex colimit. The general theorem tensors these cocones,
uses finality of the natural-number diagonal, and checks the augmentation equation
before comparing with the chosen colimit. The empty list uses the constant identity
cocone. No existing definition or statement changes, and no consumer adaptations
are necessary; the only consumer of the new theorem is the assigned module.

Proof imports added: `Sheaf.CategoryTheory.RingedKoszulFactorColimit`,
`WeilConjectures.Algebra.Homology.InternalHom`,
`Mathlib.CategoryTheory.Filtered.Final`, and
`Mathlib.CategoryTheory.Limits.Preserves.Bifunctor`.
The new factor module imports the existing module localization-colimit theorem and
Mathlib's localized-module and module-presheaf colimit APIs.

Validation: both modules compile cleanly together through `lcompile.py --all`
(18.9 and 19.3 seconds respectively). The factor construction includes s=0, a unit,
a zero divisor, and the zero ring: its calculation only uses the inverse of s in
its localization and the existing localization-colimit theorem. The general proof
handles r=0 explicitly. All helper definitions have actual constructions, and all
private helper proofs are complete. The chosen algebraic colimit isomorphism is
determined by its specified values on every colimit inclusion.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`CategoryTheory.exists_ringed_cech_koszul_colimit_iso`
(node `lem-weil-pbc-ringed-cech-koszul-colimit-iso`).

Added 0 holes and split off 0 unproved statements. The new public theorem
`CategoryTheory.exists_ringedKoszulFactor_colimit`
(node `lem-weil-pbc-ringed-koszul-factor-colimit`) and every helper are proved.
There is no `sorry` left in either delivered Lean module.

The proof uses the already stated theorem `ModuleCat.localization_away_colimit`
(node `lem-sc-module-localization-filtered-colimit`), whose existing proof is still
`sorry`. This is a dependency of the proved reduction, not a new hole in this
delivery. Thus the result is proved from the project's stated dependencies; it is
not claimed to be axiom-free independently of their remaining obligations.

## No longer needed

Removed proof import `Sheaf.Algebra.Homology.TelescopeColimit` and removed
`lem-pc-complex-hocolim-colimit` from this node's proof dependencies. A strict
complex colimit isomorphism needs no comparison with a homotopy colimit. The parent
`RingedCechKoszulDualLimit` still uses that telescope theorem separately, so this
removal does not claim that its module is globally unreachable.

The existing Koszul-system definition remains used. The extended-Cech definition
and tensor-closed theorem are now recorded explicitly because the proof uses them.
No node realizing the unit's statement or a required unit proof step is bypassed.
No other original import or declared proof dependency is discarded.

## Where the brief, the DAG or earlier work was wrong

The previous DAG attached a homotopy-colimit comparison to this strict-colimit
statement. That dependency belongs to the parent's separate telescope comparison.
The actual missing work here was the sheafified one-section fraction cocone and
its compatibility with finite tensor products. Both calculations are now Lean
proofs. No false statement or definition repair was needed.

General tools used from other units are the existing algebraic theorem
`lem-sc-module-localization-filtered-colimit` and the sheaf tensor-closed theorem
`lem-pc-sheaf-modules-tensor-closed`; they supply localization of modules and the
tensor-Hom adjunction, respectively. The proper-base-change unit supplies no
alternative declaration for these general tools. Module sheafification is the
Mathlib-backed definition `def-weil-presheaf-modules-sheafification`. No
maintainer-owned tool approval field was added or changed.

## New nodes

`lem-weil-pbc-ringed-koszul-factor-colimit`, in
`dag/nodes/sec-proper-base-change/`, records the proved one-section
augmentation-compatible colimit. Its source is Stacks Tag 0913,
`lemma-extended-alternating-Cech-is-colimit-koszul`; its statement, three proof
steps, dependencies, search results, and Lean attachment accompany the new module.
The one-section result is strictly part of the finite-list tensor induction and
is fully proved in this delivery. Blueprint searches for Koszul results found no
existing blueprint node stating this factor cocone theorem. The inherited
completed-pullback ancestor is recorded through the existing comparison chain;
`blueprint_refs.py ancestor` cannot reconstruct that chain automatically because
the recent stage-3 nodes put module names in `created.item`.

No change record is needed: no existing statement or definition was altered.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
