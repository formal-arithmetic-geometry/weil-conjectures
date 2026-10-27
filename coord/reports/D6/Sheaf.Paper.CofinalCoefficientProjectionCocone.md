## What changed

Proved `AlgebraicGeometry.ProEtale.sp_cofinal_coefficient_projection_cocone` in
`Sheaf.Paper.CofinalCoefficientProjectionCocone`, preserving its full signature and
`spCofinalCoefficientMap` verbatim. All new helpers are private and proved.

The proof constructs the ideal inclusions from the given unit factorization, applies
quotient arithmetic for representative formulas, finiteness and annihilation, and
sheafifies an underlying set section for sectionwise surjectivity. Constant scalar
cones and cancellation prove both cross-tower reduction equations. The completed
projection equation follows from the normalization of
`sp_completed_coefficient_limit` and the existing
`completedIntegralFiniteQuotientHom_ext`, instead of constructing another cofinal
comparison. Remaining equations are limit cone naturality and functor laws.

Added private proof imports for the finite-quotient extensionality theorem, ring
colimits, filtered colimits and transport of sheafification across a small site
model. The latter transport retains the independent site and coefficient universes.
Updated the item's DAG proof and dependencies to this argument. No public import,
public interface, definition, consumer, source-library file or unit route changed.

Validation: single-file server compilation through lcompile.py; delivery preflight
also checks every added declaration's axioms. Signature comparison against the
shared source confirms the theorem signature is unchanged. Line lengths are at most
100 characters. Edge cases retained: e=1, ramified e>1, n=j=0, equality of the
exponents, identical transition indices, arbitrary coefficient/site universes, and
empty T. In particular no cancellation of ell or nonempty-site assumption occurs.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.sp_cofinal_coefficient_projection_cocone`
(node `lem-sp-cofinal-coefficient-projection-cocone`).

Zero sorry left in the item, zero holes added, zero split-off statements.

## No longer needed

Removed redundant private imports:
- `Mathlib.CategoryTheory.Sites.Sheafification`;
- `Mathlib.RingTheory.Ideal.Quotient.Operations`;
- `Mathlib.CategoryTheory.Limits.HasLimits`.

Their necessary basic interfaces are already available through the retained imports.
No project module is withdrawn.

The direct proof dependency
`det-prop-sfb-qlbar-colimit-x-integral-limit` and its old top-level `tool_uses`
entry are no longer needed by this proof: the already normalized ell-limit
comparison and finite-quotient extensionality supply the projection equality.
The integral-limit node remains a statement dependency, its public import is
preserved, and it is still needed by the coefficient definitions. No claim is made
that it or its module becomes globally unreachable.

All other declared proof dependencies remain needed. In particular
`def-pur-sheaf-inverse-limit` supplies the limit API and
`lem-pc-sites-sheafification-underlying-sets` supplies the forgetful-sheafification
comparison used to sheafify the set section.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original step 4 suggested rebuilding
the cofinal comparison, but the existing normalized comparison and proved
finite-quotient extensionality already imply the needed equality. The DAG is
updated accordingly. Direct construction of the forgetful sheafification instance
on the large pro-etale category misses the required universe-sized colimits;
constructing it on its small model and transporting it resolves this without
restricting universes or disabling transparency checks.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
