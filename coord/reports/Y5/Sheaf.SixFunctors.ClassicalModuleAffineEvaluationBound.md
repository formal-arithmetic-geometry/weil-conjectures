## What changed

Proved `AlgebraicGeometry.ProEtale.classical_module_affine_evaluation_bound` with its
signature and evaluation definition unchanged. Added two fully proved private helpers:
`etale_fixed_isZero_of_ringed` transports an injective resolution through the étale
constant-ring module equivalence and reflects zero cohomology after forgetting scalars;
`evaluation_isZero_of_fixed` transports the given pro-étale resolution through the
constant-ring restriction equivalence and then restricts scalars along inverse ULift.

The main proof descends the classical fixed-module sheaf, applies the stated étale
module bound, uses the upstream bounded-below global-cohomology comparison and pullback
coherence, and identifies ambient evaluation by the upstream localization lemma.
The DAG proof and proof dependencies now describe these exact steps. All new imports
are proof-only imports. No statement, public visibility, definition, consumer, or target
changed. No change record or consumer adaptation is required.

The retained Lean proof was checked against the current sources, and its unchanged
public signature was compared verbatim. A fresh lcompile.py run compiled it cleanly
in 6.6 seconds. It contains no sorry. The theorem docstring was aligned with the
implemented route and its DAG record. The required delivery preflight checks the
axioms of all declarations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.classical_module_affine_evaluation_bound`
(node `lem-sfb-classical-module-affine-evaluation-bound`).
Added 0 holes and split off 0 statements. No sorry remains in the delivered module.
The imported étale bound remains an existing stated dependency; this delivery does not
claim its proof or transitive axiom closure is complete.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`;
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`;
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.

The unused temporary import `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives` was
also removed before delivery. The mapped fixed-module resolutions use the existing
Grothendieck fixed-coefficient sheaf infrastructure; no separate ringed-site
Grothendieck or enough-injectives input is needed. Removed direct proof dependencies
`lem-weil-pbc-ring-sheaves-grothendieck`, `lem-sp-grothendieck-enough-injectives`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-pe-constant-left-module-inverse-image`, and
`lem-weil-pbc-right-derived-plus-injective` from this node, together with their obsolete
top-level tool approvals. The exact constant-ring equivalences and classical
right-derived-resolution API replace them.

The geometric content of `lem-weil-pbc-proetale-restriction-injectives` remains needed
and stays in the DAG: the proof uses its already proved upstream localization
specialization rather than importing the larger statement module. Likewise the
bounded-below comparison remains needed and is used through its already proved
upstream degree-zero global-cohomology API. No unit statement or unit proof step is
bypassed. These are direct dependency/import prunings, not claims that their modules
are globally unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The planned argument is mathematically correct, but its two module encodings do not
match definitionally: the main statement and étale bound use modules over a constant
ring sheaf, while classical descent and bounded-below comparison use fixed-ring
ModuleCat-valued sheaves. The proof explicitly transports injective resolutions
through the existing equivalences. It never assumes that forgetting a module
injective to an abelian sheaf preserves injectivity. Exact forgetful functors are used
only to commute with homology and reflect zero modules.

The generic upstream comparison/localization lemmas already supply the needed
bounded-below and slice computations. There is no need to construct a one-object
affine presentation or an integer-indexed representative in this file. The field,
prime, annihilator, finiteness, dimension, and affine étale hypotheses are all passed
to the unchanged stated étale bound; the generic transport also handles the zero ring
and empty scheme/object without extra hypotheses.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
