## What changed

Completed the three theorem proofs in
`lean/Sheaf/Paper/ConstructibleCoefficientSiteSquare.lean` without changing their
signatures, public imports, existing definition, or existing docstrings.

`constructibleCoefficientSheaf` uses the already proved source scalar-extension
comparisons and constructibility instance. It transports each specified finite
constant model through the étale slice equivalence, commutes scalar extension
with the stratum and covering pullbacks, and transports the resulting extended
constant model back. The extended module is finite over the finite target ring.

`constructibleSiteComparison` uses the source's proved forward constructibility
comparison. The existing finite-model local-constancy and finite-stalk theorems
convert this to the intrinsic fixed-module predicate. The arbitrary specified
cover/model clause uses the canonical comparison/pullback isomorphisms and the
pro-étale slice equivalence. A zero-stratum input forces the scheme empty; the
one-stratum identity partition and the fact that every sheaf on its empty site
is zero supply precisely the requested zero constant model.

`constructibleCoefficientSiteSquare` computes cohomology as the cokernel of the
incoming map into the outgoing differential's kernel. Kernel/cokernel closure,
the constructibility-encoding bridge, and localization's homology comparison
prove the étale assertions. Exact comparison commutes with homology, and
transport of local models and geometric-stalk colimits gives the intrinsic
pro-étale assertions. Zero middle terms give every stated vanishing assertion.
All helpers are private and fully proved.

Updated the item's DAG proof, proof dependencies, proof origin, and removed
obsolete top-level tool approvals to match this route. No other module changes.

Validation: lcompile.py compiled the final module successfully with no warnings
in 19.5 seconds. The delivery tool performs its independent compile and axiom
checks. No flatness hypothesis, derived scalar-extension identification, or
positive-stratum hypothesis was added. Empty schemes, empty partitions, zero
coefficient rings, zero complexes, and one-degree intervals remain covered.

## Proved and sorry left

Closed all 3 original holes:

- `AlgebraicGeometry.constructibleCoefficientSheaf`.
- `AlgebraicGeometry.constructibleSiteComparison`.
- `AlgebraicGeometry.constructibleCoefficientSiteSquare`.

Each is attached to `lem-sp-constructible-coefficient-site-square`.
Remaining holes in the item: 0. Holes added: 0. Split-off statements: 0.
This is a proof delivery, not a decomposition.

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.Paper.ProEtaleSheafificationTensorComparison`.
- `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `Sheaf.Paper.ProEtaleConstantModuleEncoding`.
- `Sheaf.Paper.ProEtaleConstantModuleConstructibility`.
- `Mathlib.CategoryTheory.Sites.LocallyBijective`.

The first four planned constant-presentation/tensor arguments are replaced by
proved source scalar-extension APIs. The source comparison API already provides
the pullback isomorphism, so its separate coherence wrapper is unnecessary.
The fixed-module finite-model lemmas give local constancy and finite stalks
directly, so no ringed-module encoding or its constructibility equivalence is
needed. The locally bijective sheafification criterion is unnecessary.

Removed these planned proof dependencies and their obsolete tool approvals
where applicable:

- `def-sf-site-constant-module-functor`.
- `lem-weil-pbc-site-module-presheaf-sheafification-exact`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-sf-proetale-sheafification-tensor-comparison`.
- `lem-weil-pbc-algebraic-inverse-image-tensor-comparison`.
- `def-weil-pbc-etale-constructible-sheaf` (still a statement dependency).
- `lem-pur-etale-proetale-cover` (the proved source covering inclusion is used directly).
- `lem-weil-pbc-proetale-constant-module-encoding`.
- `lem-weil-pbc-proetale-constant-module-constructibility`.
- `def-weil-proetale-constructible-sheaf` (still a statement dependency).
- `lem-weil-pbc-site-sheafification-iso-locally-bijective`.

No module is withdrawn. These are dependencies removed from this item's proof;
other consumers and unchanged public imports may still need their modules.

## Where the brief, the DAG or earlier work was wrong

The planned finite-presentation and ringed tensor comparison route is unnecessary:
`WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible` already proves
constant-model, pullback, and constructibility preservation for the actual
ordinary scalar-extension functor used by the item's definition. The proof uses
these source declarations unchanged. The source's forward site-comparison proof
also already supplies finite models on a global stratification.

The old blueprint filename in the existing docstrings is absent from the current
latest snapshot. The current constructible-comparison proof has been reorganized;
the exact finite-model and homology argument required by this item is implemented
as stated in its DAG node. No mathematical statement correction was needed.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
