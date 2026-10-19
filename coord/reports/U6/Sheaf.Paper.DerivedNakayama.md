## What changed

Proved `AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
in `Sheaf.Paper.DerivedNakayama`, preserving its signature and public imports.
Two proved private helpers construct the normalized two-term resolution from a
short exact sequence and compare zero tensor reduction with zero derived scalar
extension on a K-flat representative. The isomorphism clause uses the existing
cone-closure assertion, triangulated tensor reduction, and the zero-cone criterion.
The DAG proof now follows these actual steps. No other module is changed. The two large derived-functor implementations are
locally marked irreducible; all uses go through their existing comparison API.
This introduces no global attribute or interface change.
The conservative preflight requested a record for these top-level commands:
`coord/changes/U6-derived-nakayama-local-proof-context.md` documents their local
scope and checks both downstream consumers; neither needs adaptation.

Added proof imports of `Mathlib.Algebra.Homology.Double`,
`WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic`, and
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` for the explicit
complex, acyclicity detection, K-flat tensor model, and exact tensor functor.

Validation on 2026-10-19: the retained proof was checked against the current
source statements and compiled through `lcompile.py` in 40.9 seconds, exit code
zero, with no diagnostics. Its original theorem signature is unchanged, every
Lean line is at most 100 characters, and the module contains zero `sorry` tokens.
The resumed delivery dry run also passed compilation, the axiom probe and server
preflight, with review class CODEX for the node and local-context record.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
(node `sk-lem-pe-derived-nakayama`). Both private helpers are proved.
Holes closed: 1. Holes added: 0. Holes remaining in this module: 0.
There are no new modules or split-off statements. The proof uses the existing
statements `derived_nakayama_resolution` and `derived_nakayama_first_reduction`;
their pre-existing holes remain their own items.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
  (`lem-weil-pbc-standard-quotients-perfect`): the existing pro-etale resolution
  already supplies the exact sequence needed here. Repeating its ordinary
  coefficient argument adds no information to this proof. Its obsolete top-level
  `tool_uses` entry is withdrawn.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`
  (`def-weil-pbc-strict-perfect-coefficient-package`): the unchanged theorem asks
  for the explicit bounded rank-one representative and normalized augmentation,
  rather than a separate strict-perfect package. Those data are constructed
  directly; this definition is not used by the proof.

The two existing resolution and first-reduction dependency imports stay. The
already omitted `lem-weil-pbc-levelwise-isomorphism-cones` is also unnecessary:
the cone argument uses only the first reduction. These are local dependency
prunings; no claim is made that other parents no longer need those modules.

## Where the brief, the DAG or earlier work was wrong

The original plan says the first-reduction assertion applies directly to
`reductionFunctor`. Its Lean statement uses `AdicCompletion.derivedReduction`,
whose codomain retains the finite coefficient action. The two functors are not
definitionally identical. The proved K-flat helper identifies their vanishing,
using pullback/restriction compatibility and the underlying scalar-extension
versus tensor isomorphism. Applying the cone argument avoids assuming an
unproved comparison on morphisms.

Edge cases checked in the argument: the first exponent is n+1 even at n=0;
the complex has no terms outside -1 and 0; the empty scheme, zero complex,
identity morphism, and arbitrary unbounded representatives require no extra
hypotheses. The unit route (resolution, vanishing, complete cone) is retained.
No definition or statement changes, consumer adaptations, or new nodes.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
