## What changed

In `Sheaf.CategoryTheory.ToposFiniteFreeCompactConstituents`, proved four constituent
assertions using Mathlib adjunction mates and exact localization. No public statement or
non-theorem definition changed. The only added declaration is a proved private helper
`localized_unit_isIso`.

`restrictionPushforward_isIso` follows from `tensorPullbackInv_isIso` by the iterated-mate /
conjugation identity. `betaInv_isIso` is the inverse double mate of the existing isomorphism
`tau`. `open_units_isIso` localizes the already invertible ordinary units, checking the
termwise unit componentwise. `beta_unit` inverts the defining mate unit equation.

The node copy records these formal reductions while preserving the original plan for
its remaining unproved assertions. Five unused private proof imports were removed.

## Proved and sorry left

Closed 4 of the original 11 holes, added 0 holes, and split off 0 statements:

- `CategoryTheory.ToposFiniteFreeCompact.restrictionPushforward_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.betaInv_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.open_units_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.beta_unit`

The following 7 original holes remain, all attached to
`lem-pur-topos-finite-free-compact-constituents`:

- `CategoryTheory.ToposFiniteFreeCompact.scalar_exact`
- `CategoryTheory.ToposFiniteFreeCompact.tensorPullbackInv_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.restrictionOpen_isIso`
- `CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactConstituents`
- `CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactCoordinates`
- `CategoryTheory.ToposFiniteFreeCompact.chi_comp`
- `CategoryTheory.ToposFiniteFreeCompact.beta_comp`

The four closed assertions have complete proofs from existing declarations. In particular,
`restrictionPushforward_isIso` still depends on the original, unproved
`tensorPullbackInv_isIso`; no claim of removing that dependency is made. There are no
new public declarations, nodes, or holed private lemmas.

## No longer needed

Removed unused private imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.CategoryTheory.RingedOpenScalarAdjunction`
- `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`

The completed mate and unit arguments do not use these modules. No declaration or module
is withdrawn. The original DAG dependencies are retained for the seven unfinished parts,
whose mathematical plans still refer to them; they must not be globally pruned on the
strength of these four local proofs.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The proposed K-injective and sectionwise constructions
are unnecessary for the four completed assertions: the recorded mate definitions and
ordinary invertible units already imply them formally. The source and target statements
are unchanged, including the empty-basis case. No forced adaptations were made.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
