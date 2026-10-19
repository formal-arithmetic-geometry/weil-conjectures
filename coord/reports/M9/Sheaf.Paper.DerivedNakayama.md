## What changed

Proved `AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
in `Sheaf.Paper.DerivedNakayama`, preserving its signature, universes, public imports,
and the unit route. The private `twoTermResolution` constructs the double complex of
an arbitrary short exact presentation and proves that its normalized augmentation
is a quasi-isomorphism, checking degrees -1, 0, and all remaining degrees separately.
The resolution theorem supplies the coefficient sequence and natural cone comparison.

Private coefficient and reduction comparisons identify scalar-extension reduction
followed by exact restriction with the stated tensor reduction. This uses the already
proved generic `CategoryTheory.Mod.residueDerivedTensorIso` from
`Sheaf.Paper.IntegralResidueTensorPresentation`, not its specialized residue-exchange
statement. Exact faithful restriction reflects derived zero objects and isomorphisms
by commuting with all homology functors. The existing first-reduction theorem then
proves the two final clauses. No boundedness, constructibility, or invertibility
hypothesis was added.

Added proof-only imports of IntegralResidueTensorPresentation, Mathlib's Double and
ReflectsIso.Balanced, and the source library's derived ExactFunctor API. Updated the
item node's proof, proof dependencies, proof origin, and obsolete tool approval list.
No definitions or signatures of existing declarations changed; no consumer adaptations.
The added private helper universes, namespace opening and section variables are
recorded in `coord/changes/M9-derived-nakayama-private-proof-context.md`, including
both downstream consumers. The dry-run static checker requires this record for
command changes even though the existing public declaration retains its signature.

Validation: the complete module compiled cleanly through lcompile.py in 24.7 seconds.
No sorry, axiom, unsafe declaration, or skipped kernel check occurs in the delivery.
Private helper data are explicit constructions, not choices from existence theorems.
Edge cases include the zero presentation, the empty scheme, exponent one, zero objects,
and identity morphisms; the general short exact argument and natural comparisons
cover them without extra assumptions.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
(node `sk-lem-pe-derived-nakayama`). Proved 1 of 1 original sorries; zero added;
zero split off; zero remaining in the delivered module. This is a proof from existing
stated dependencies, including the existing resolution and first-reduction theorems;
it does not claim those imported theorems have become sorry-free.
All private helpers are fully proved or explicitly constructed.

## No longer needed

Removed direct proof imports of
`Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
(node `lem-weil-pbc-standard-quotients-perfect`) and
`Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`
(node `def-weil-pbc-strict-perfect-coefficient-package`). Their nodes are removed from
this item's proof dependencies; the obsolete standard-quotients tool approval is
withdrawn. The pulled-back short exact sequence directly constructs the requested
bounded rank-one resolution and its augmentation, so neither the separate ordinary
ring-module resolution nor the site perfectness packaging is used by this proof.
These are direct-dependency removals, not claims that the modules are globally
unreachable: the resolution dependency can still import them for its own argument.
No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The two uses of first reduction have different Lean codomains: the dependency uses
finite-coefficient derived scalar extension, whereas this item uses tensor reduction
in the integral derived category. They are not definitionally identical. The proof
now supplies the canonical comparison and uses conservativity of exact restriction;
applying the dependency directly would not typecheck. The already proved generic
tensor-presentation construction is used as a tool for this interface comparison.
The unit's resolution/vanishing/cone-isomorphism route is retained through its
existing resolution and first-reduction declarations. No mathematical statement was
found false and no new node or new hole was needed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
