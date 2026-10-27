## What changed

Proved `AlgebraicGeometry.Scheme.adicPerfectQuotientComplex_terms_projective` in
`Sheaf.Paper.AdicPerfectQuotientTermsProjective`, preserving its complete signature,
existing docstring and public import. The proof uses the actual ordinary quotient
functors in the statement.

Three proved private helpers establish projectivity of the slice unit from the
set-sheaf evaluation hypothesis, transport of the unit across a ring-sheaf isomorphism,
and the explicit scalar-extension unit isomorphism. The last calculation uses the
existing tensor restriction formula and module-sheafification counit; it is the same
sectionwise calculation as the private `scalarUnitIso` in
`Sheaf.Algebra.Homology.LocallyFreeDerivedScalars`, without importing its unrelated
derived machinery.

The main proof splits each finite projective term off a finite free module, maps the
retract through constant realization and the ordinary coefficient functors, identifies
the resulting finite free object with a finite product of quotient units using the
proved `strictPerfectConstantFiniteFreeComparison_isIso`, and applies projectivity of
finite biproducts and retracts. Slice additivity is supplied explicitly by the proved
`ringedOverFunctor_additive`. Projectivity of the finite biproduct is proved by
lifting its coprojections individually, so the argument does not depend on a
small-index projectivity instance at a larger Hom universe. The proof covers rank zero, the zero ring, the unit
ideal and an empty slice. No boundedness assumption is needed.

Added proof imports:
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` for
  preservation of epimorphisms when forgetting module structure;
- `Mathlib.Algebra.Category.Grp.Abelian` and
  `Mathlib.Algebra.Category.Grp.EpiMono` for the abelian-sheaf epi criterion;
- `Mathlib.CategoryTheory.Sites.EpiMono` for passage to an epi of set sheaves;
- `Mathlib.CategoryTheory.Preadditive.Projective.Basic` for projective biproducts
  and retracts;
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` for additivity of
  restriction of scalars;
- `Mathlib.RingTheory.Finiteness.Cardinality` for finite free presentations. No existing shared module or definition was changed.
Updated the item's DAG proof and proof dependencies to describe the actual argument.

Searches: LeanFinder found the algebraic/categorical projectivity bridge and general
projectivity APIs; Loogle found `CategoryTheory.Retract.projective`. Mathlib and both
project roots were searched for constant finite-free comparisons, scalar-extension
units and weakly contractible projectivity. The existing large-pro-etale-site
`sf_weakly_contractible_projective` does not apply to this coefficient-sized slice.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.adicPerfectQuotientComplex_terms_projective`
(node `lem-sfb-adic-perfect-quotient-terms-projective`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean file.
All three new private helpers are completely proved.

Validation: the delivered module compiled cleanly through `lcompile.py` in 11.8 s,
with exit code 0 and no warnings (result `7557357062ca9887b71c8cac`).

## No longer needed

No original imports were removed and no modules were withdrawn. The exploratory
proof import `Mathlib.Algebra.Category.ModuleCat.Products` was removed: the existing
constant finite-free comparison already supplies the needed tuple identification.

The declared proof dependency
`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact`
(`Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`) is not needed
by this proof: it is specialized to the original large pro-etale site and a fixed
coefficient universe, whereas the hypothesis here concerns the coefficient-sized
slice. Its short general-site argument is proved directly for that slice. Removed
this node from the item's proof dependencies; this does not assert that its module
is unused elsewhere.

The constant-completion dependency remains for the actual ordinary `change` functors
and their additivity. The strict-perfect coefficient package and canonical constant
ring transport and additive slice restriction are recorded explicitly as proof dependencies. No derived-completion
equivalence, K-projectivity theorem or bounded complex model is used.

## Where the brief, the DAG or earlier work was wrong

The planned dependency for weakly contractible evaluation has the wrong site and
universe for direct application. The mathematics of the plan is valid; its
terminal-section proof works directly on the slice and is implemented here.
Tags 09C5 and 09C6 supply the surrounding adic finite-projective model argument;
the general exact-evaluation fact used in the private helper is Stacks Tag 0946.
There is no statement correction, definition repair or change of the unit's route.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
