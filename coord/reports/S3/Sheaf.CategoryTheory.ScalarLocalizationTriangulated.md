## What changed

Proved `CategoryTheory.ScalarLocalization.exists_triangulated_scalarLocalization`
in the assigned module, preserving its complete signature and all public imports.
Added the private, fully proved helpers `all_shift_linear` and `rationalComparison`.
The comparison identifies the raw tensor-Hom category with the existing Verdier
rationalization using its proved `Rationalization.tensorHomEquiv`. This transfers
Q's localization universal property. `HasShift.induced` then supplies exactly the
specified tensor shift and identity comparison, and Mathlib's triangulated
localization construction supplies the remaining structures and triangle criterion.

Added only the proof import
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`.
Updated the item's DAG proof, proof dependencies and proof origin to this shorter
route. The item's existing docstring retains its original longer proof plan; the
implemented route is recorded in the updated DAG and this report. The scoped
`linter.unusedVariables` setting suppresses warnings about the unchanged named
instance binders in the existential statement; it does not change the statement.

Validation: the final module compiles cleanly through `lcompile.py`, without
warnings. Import-direction checks permit the comparison dependency. A separate
sandbox probe checked the theorem's axioms: standard axioms and inherited
`sorryAx` only. The inherited holes are in the existing scalar-category theory,
not new admissions in this delivery. The imported rationalization construction,
fraction lemmas and tensor-Hom equivalence have complete source proofs. Independent
object, morphism and coefficient universes are retained. Zero and nilpotent p,
unit p, zero rings and zero categories are all covered, since no nonzero or
regularity assumption is used. There is no new object chosen from an unproved
existence theorem: the private comparison is a concrete functor with proved laws.

## Proved and sorry left

Closed 1 of the original 1 holes:
`CategoryTheory.ScalarLocalization.exists_triangulated_scalarLocalization`
(node `lem-weil-linear-scalar-localization-triangulated`).
Added 0 holes and split off 0 statements. There are no remaining `sorry`s in
any delivered Lean file. This is a proof from existing declarations, not a
new decomposition. It still depends on the preexisting scalar-category
construction and its named proofs, as intended by stage 3.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`;
- `Mathlib.RingTheory.Localization.BaseChange`;
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`;
- `Mathlib.CategoryTheory.Localization.Triangulated`;
- `Sheaf.CategoryTheory.LinearScalarLocalization`.

The last and the localization/base-change APIs needed internally remain available
through the retained statement import or the new proved rationalization import.
This delivery does not claim that all transitive uses of those modules disappear.

The item's proof no longer needs these old declared dependencies as separate steps:
`def-pur-saturated-triangulated-localization`,
`def-weil-pbc-module-localization-away`,
`lem-weil-pbc-hom-into-triangle-exact`, `lem-weil-pbc-five-lemma`, and
`def-sp-abelian`. The existing rationalization supplies the Ore and compatibility
arguments and arbitrary-functor localization property, so the original direct
scalar MS1--MS6 verification and localized Hom five-lemma argument are unnecessary.
The raw scalar construction, the module-tensor comparison and the general
triangulated-localization theorem remain used. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement correction or definition repair was required. The original plan
missed an already fully proved source-library construction:
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`.
Its tensor-Hom equivalence gives a much shorter route than repeating all the
scalar fraction-calculus axioms. Only linearity of shift by one was assumed;
the new proved helper derives linearity of all integer shifts before applying
that construction. The typing unit `sk-def-sf-operations` has no realized proof
steps that this shorter below-unit argument would bypass. The added rationalization
nodes are existing closed constructions or tools; no blueprint unit is changed.

The axiom probe confirms that closing this module's hole does not make the
preexisting scalar-category construction axiom-free: it still contains named
admissions. Those are unchanged dependencies, with no new hole introduced here.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
