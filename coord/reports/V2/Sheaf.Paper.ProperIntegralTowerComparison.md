## What changed

Replaced the single `sorry` in
`WeilConjectures.ProperIntegralTower.proper_integral_tower_comparison` by the
nine-clause argument, using the fixed strict systems and total-limit model
already constructed in the module. All existing statements and definition bodies
are unchanged.

Validation: both new statement modules compile, and the assigned module compiles
cleanly with no warnings (40.6 seconds). The existing theorem signature and all
existing definition bodies were compared verbatim with the shared source.

The finite transition square follows by cancelling the compact evaluation
isomorphism and using naturality of the strict tower transition. Naturality of the
actual total-limit projection gives the native projection equation. Two-variable
naturality of the recorded scalar adjunction gives both reduction equations. The
recorded projection equation cancels the inverse native comparison. The recorded
reduction normalization uses the chosen calculus's `counit_projection` and the
published `CompactRealizationSpec`, rather than adding another normalization
assumption.

Two smaller steps are stated in new modules: identity-open finite evaluation,
and the two prescribed successor-transition evaluations. Their statements apply
to arbitrary unbounded inputs and use exactly the existing normalized comparisons.
They neither restate the integral comparison theorem nor choose any new data.

## Proved and sorry left

This is a decomposition, not a completed proof of the import closure. Closed one
existing hole, in
`WeilConjectures.ProperIntegralTower.proper_integral_tower_comparison`
(node `lem-weil-proper-integral-tower-comparison`). No hole remains in the assigned
module. Added two holes, each exactly a named public theorem body:

- `WeilConjectures.FrobeniusExchange.identity_open_system_evaluation`
  (`lem-weil-identity-open-system-evaluation`).
- `WeilConjectures.FrobeniusExchange.proper_system_evaluation_transitions`
  (`lem-weil-proper-system-evaluation-transitions`).

The packet therefore closes one hole and adds two (net minus one). The proof from
these steps to all nine conclusions is complete. Existing dependencies retain
their own previously recorded holes.

Edge cases checked in the new statements: the zero complex, empty schemes,
identity proper morphisms, and n = 0 (positive quotient exponent one). Neither
statement requires bounded finite reductions or claims a reduction comparison is
invertible. Neither introduces a finite-field structure on X or Y beyond the
ambient datum used to name the completed-tower transition.

## No longer needed

The proof does not separately use the DVR/completeness argument: the existing
calculus and system operations already supply the fixed models. It also does not
separately invoke the general coefficient-system comparison, ringed strict-tower
homotopy-limit existence theorem, derived-tower counit theorem, or pro-etale
inverse-image construction. Those are retained where the existing constructions
need them; this packet makes no claim that their modules are globally unused.

Removed direct proof imports:
`Sheaf.Paper.CoefficientSystemDerivedComparison`,
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`Sheaf.CategoryTheory.DerivedTowerCounitProjections`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, and
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.

The item's direct proof dependencies are replaced by the actual formal argument.
Old nodes no longer directly used there are
`lem-weil-l-adic-extension-complete`,
`lem-weil-l-adic-extension-integers-dvr`,
`lem-pur-coefficient-system-derived-comparison`,
`def-weil-proetale-inverse-image`,
`def-weil-derived-direct-image`, `def-weil-extension-by-zero`,
`lem-weil-proper-finite-normalization`,
`def-weil-integral-rational-qbar-compact-support`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and
`lem-coef-derived-tower-counit-projections`.
Some remain dependencies of the two new finite coherence statements or the
unchanged constructions. Obsolete top-level tool approvals are removed from the
item; the calculus and scalar-adjunction approvals remain. No module is withdrawn
and no blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old five-step proof is mathematically appropriate but its first two construction
steps are already embodied in the published definitions. The remaining Lean glue
requires explicit compatibility with those particular finite evaluation mates and
successor transitions. The generic coefficient comparison theorem constructs a
separate presentation; importing it alone does not identify that presentation with
these published maps. The new statements isolate exactly these identification
steps. No existing statement was found false or altered.

## New nodes

`lem-weil-identity-open-system-evaluation` states only the finite-evaluation square
for the adjunction-normalized identity-open isomorphism, before applying system
direct image or total inverse limit. Its proof transposes the square using the
finite open adjunction and compares the ordinary section-normalized units.

`lem-weil-proper-system-evaluation-transitions` states only the compact and ordinary
successor-transition squares for their specified evaluations, before comparing the
two towers or taking a limit. Its proof uses one K-flat quotient system and the
simultaneous direct-image and open evaluation mates, then exact completed
restriction. Sources are the current blueprint's proper-coincidence paragraph,
Zheng Construction 4.1 and Lemma 4.10, and Stacks 03DI, 03CY, 0D6E.

Mathlib searches: LeanFinder returned unrelated opens-adjunction and locally
constant counit identities; Loogle supplied the generic naturality lemmas used in
the combining argument; grep found no Mathlib declarations for the specified
comparisons; LeanSearch returned general adjunction and adic/direct-limit results.
Local searches also read the existing geometric-fiber-specific identity-system
mate and `IntegralProperTowerTransition`; their inputs and fixed models differ.
The blueprint searches found no matching identity-open evaluation node, and the
quotient-transition search results describe different comparisons. Both new nodes
carry the searches, source, full proof in words, and their exact Lean attachment.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
