## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback_locallyConstant` in
`Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`, with its signature unchanged.
The proof preserves the supplied index set, the actual base-changed site objects, and
all of the specified modules `M i`.

The shorter route uses the proved canonical comparison
`proEtaleModuleRestriction_pullback`, then the concrete slice-site equivalence,
`upperStarIsoLocalizationRestriction`, `upperStarComp`, and the existing constant-sheaf
comparison. It uses the proved localized constant-scalar restriction and sheafification
comparison helpers from `ProEtaleConstantModuleConstructibility` through `import all`;
it does not apply the constructibility theorem or its finite-stalk assertions.
The local-constancy conclusion is assembled directly from the constructed covering
and its isomorphisms. No new declarations or intermediate holes were added.

The public imports now name only the inverse-image and local-constancy interfaces
needed by the unchanged statement. All new proof imports are private to this module.
The node's proof and proof dependencies record the implemented route, including the
constructibility module solely for its proved private constant-comparison helpers.
The import change record is
`coord/changes/J7-proEtalePullbackLocallyConstant-imports.md`.

Validation: the delivered module compiles without warnings in 9.3 seconds. All three
unchanged direct importers compile against it: `ExplicitExceptionalPreservation`
(16.8 seconds), `FiniteTorInternalHomAnyField` (4.0 seconds), and
`ProEtaleConstructibleExactClosure` (3.5 seconds). These consumer copies live only
in the sandbox validation directory and are not delivered. Final delivery preflight
and axiom checks are run by `deliver3.py`.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.proEtaleConstantModulePullback_locallyConstant`
(node `lem-exc-proetale-pullback-locally-constant`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean file.
The conclusion retains each given `M i`, so all `hfinite i` remain valid without any
transport of their carrier types. The proof actually works for arbitrary module models.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  the proof does not transport derived functors or use the intrinsic realization.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  the finite coefficient normalization is already built into the proved encoding comparison.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`:
  the conclusion uses the original ringed-module local-constancy predicate directly.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`:
  the existing fixed-module pullback and its adjunction provide the needed functor.
- `Sheaf.Paper.LocalizeRingedSiteMorphism` and
  `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`:
  the concrete slice equivalence and scheme pullback-composition square suffice.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` and
  `Sheaf.SixFunctors.GeometricInverseImageConstantModule`:
  after the proved coefficient-encoding comparison, the existing fixed-module
  constant-sheaf pullback isomorphism gives the same model.

The following original direct proof dependencies are no longer needed by this proof:
`lem-weil-pbc-left-exact-site-inverse-image-tensor`,
`lem-sfb-geometric-inverse-image-constant-module`,
`prop-weil-pbc-proetale-constant-ring-map`,
`lem-pe-constant-left-module-inverse-image`, and
`lem-weil-pbc-localize-ringed-site-morphism`.
Their obsolete top-level tool-use approvals are withdrawn from this node.
This is local pruning: other consumers can still need these modules and nodes.
The statement's existing `stmt_deps` are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original general ringed-site route is mathematically correct but requires
additional comparisons between the chosen tensor construction and a generic geometric
module inverse image. The already proved constant-module encoding comparison supplies
exactly that identification, including the canonical scalar normalization. In those
coordinates the concrete small-site equivalence and the cartesian-square composition
argument yield the required isomorphisms without the general localized tensor theorem.

Checked the source at Stacks Tag 093R (its proof is omitted), the item and its unit
record. The unit record has no realized statement or proof-step attachment for this
node. The replacement changes only the proof below the unit level. No target statement,
definition, model, or finiteness condition was changed. Empty schemes, empty covering
members, empty index sets and the zero ring are included; no points are chosen.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
