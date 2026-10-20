## What changed

Proved `AlgebraicGeometry.Etale.internalAdjunctionEvaluation_mate_core` in
`Sheaf.SmoothPurity.InternalAdjunctionEvaluation`. The existing
`internalAdjunctionEvaluation` proof now depends on a proved mate core.
Both public signatures and their source-library constructions are unchanged.

The private `conjugate_uncurry` lemma proves the elementary mate identity from
`conjugateEquiv_counit` and naturality. The main proof unfolds the canonical exchange
component, abstracts the projection component to normalize its functor types, and
applies that identity to the composite of the three existing adjunctions. Expanding
`Adjunction.comp_homEquiv` gives the requested tensor transpose and exceptional counit.
Removed the two unused private parametrized/composite helper lemmas, and nine unused
private proof imports. Updated both nodes to record the actual argument and withdrew
their obsolete top-level tool approvals. No definitions, public interfaces, other
modules, or unit realizations were changed.

Validation: the final module compiles without warnings through `lcompile.py` in 8.3 s.
A separate axiom probe compiles in 8.8 s. Both public theorems report `propext`,
`Classical.choice`, `Quot.sound`, and inherited `sorryAx` from existing library
infrastructure; the delivery adds no axiom or local hole.

## Proved and sorry left

Closed 1 of the original 1 holes:
`AlgebraicGeometry.Etale.internalAdjunctionEvaluation_mate_core`
(node `lem-asd-internal-adjunction-evaluation-mate-core`).
The existing public `AlgebraicGeometry.Etale.internalAdjunctionEvaluation` remains proved.
Added 0 holes; split off 0 theorems. No `sorry` remains in any delivered Lean file.
This is a proof, not a decomposition.

## No longer needed

Removed these direct private proof imports:

- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`

The canonical adjunctions and canonical projection already provide the infrastructure
that the old seven-step plan reconstructed. Consequently none of the old proof-step
citations is used as a separate proof lemma in this argument:

- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-pur-rhom-global-sections`
- `def-asd-compactifiable`
- `def-weil-proper-morphism`
- `def-weil-finite-type-morphism`
- `pqf-lem-locnoeth-lft`
- `lem-amb-proper-coproducts-projection`
- `def-amb-etale-compact-support`
- `lem-pur-etale-open-derived-tensor`
- `thm-amb-etale-exceptional-adjoint`
- `lem-weil-pbc-adjunction-of-natural-bijection`
- `prop-asd-internal-adjunction`

The sole proof dependency of the public evaluation node is now the mate-core node;
the mate core uses the Mathlib adjunction API and the existing source definitions.
Withdrew these five obsolete top-level `tool_uses` entries from both node copies:
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-pur-rhom-global-sections`,
and `pqf-lem-locnoeth-lft`.

No module is withdrawn. Nodes still needed by the statements or by transitive
source-library imports remain in place; these removals do not assert that those
modules are globally unreachable. All existing `stmt_deps` are preserved.

## Where the brief, the DAG or earlier work was wrong

The old resolution-level proof plan was longer than necessary for the canonical
exchange actually used by the Lean statement: it is already defined by conjugating
the projection map along the composite adjunction. Its evaluation formula therefore
follows from the general mate identity. No mathematical statement repair is needed.
The former private parametrized/composite helpers were also unnecessary once the
projection component was abstracted before normalizing its functor types.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
