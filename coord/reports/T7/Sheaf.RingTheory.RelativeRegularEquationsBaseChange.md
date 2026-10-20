## What changed

Proved
`RingTheory.Sequence.isRegular_localizationAtPrime_tensorProduct_of_flat_quotient`
with its original public signature and public imports unchanged. Only the item
module and its existing DAG node are delivered; no definitions or consumers change.

The proof localizes A first at the contracted prime p. Quasi-regular base change
then applies directly to the local closed fibre, avoiding a separate theorem about
localizing associated-graded rings. The fibre is Noetherian because it is a
localization of a finite type algebra over a field. The existing quasi-regular
Noetherian-local criterion makes the equations regular there.

A fully proved prefix induction uses the existing essentially finitely presented
local module injectivity criterion (Stacks 046Y). Tensor injectivity with flat
cokernel then handles the arbitrary changing algebra. Tensor-quotient and
localization comparisons identify the resulting sequence with the specified one.
The maximal-ideal criterion supplies the nonzero final quotient, also for no equations.
All six private helpers are proved in this module.

`lem-trf-valuation-general-mod-injective` is used as a generic algebraic tool:
its statement is the local module criterion, with no trace-formula, valuation or
geometric hypotheses. The purity unit supplies no such local injectivity theorem.
The explicit finite-presentation witness is P = (R \\ r)^-1 A, with A_p a further
localization. The unit's own statement and realized proof steps are unchanged.

## Proved and sorry left

Closed the only original hole:
`RingTheory.Sequence.isRegular_localizationAtPrime_tensorProduct_of_flat_quotient`.

Actual count: one of one original sorries closed; zero sorries remain in the item;
zero sorries added; zero statements split off. The proof uses existing named
project declarations, some of which still contain sorry, as stage 3 requires.
No new axioms, definitions or arbitrary witness choices are introduced.

The final item compiled cleanly with lcompile.py (11.0 seconds). The local prefix
argument and tensor argument were developed and compiled separately as scratch probes
before integration.

## No longer needed

Removed direct imports:

- `Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood`;
- `Mathlib.Algebra.Module.LocalizedModule.Exact`;
- `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`;
- `WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness`.

The following original proof dependencies are no longer needed by this item:

- `lem-weil-pbc-localization-module-exact`: the proof uses existing tensor/localization
  comparisons directly and no associated-graded localization argument;
- `lem-exc-regular-sequence-principal-neighbourhood`: everything is done at A_p;
- `lem-pc-algebra-fibre-cartier-local`: 046Y supplies prefix flatness locally;
- `lem-pc-affine-flat-module-localization-preserves-flatness`: ring localization
  flatness and composition suffice for the final quotient;
- `lem-weil-pbc-localization-away-polynomial-quotient`: no principal shrinking occurs;
- `lem-weil-pbc-finite-presentation-quotient-fg-ideal`: the induction needs module
  finite presentation, obtained directly from the finite list of generators.

The two obsolete top-level tool approvals, for principal-neighbourhood spreading
and algebra-module localization flatness, are withdrawn. The new generic use of
046Y is recorded above for the independent reader and maintainer.
These are dependencies pruned from this item's proof; no assertion is made that
other target branches stop needing the same modules. No unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original plan's principal
neighbourhood construction can be replaced by the existing local module criterion
once the algebra is localized first. This also avoids developing an additional
localization API for the custom associated-graded polynomial map.

The combined proof was checked within the unchanged compilation limit. Explicit
local-ring and quotient imports, and named localization evidence, keep the
elaboration of its scalar towers manageable. No definition, timeout limit or
module boundary was changed to evade the limit. No speculative split module or node is delivered.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
