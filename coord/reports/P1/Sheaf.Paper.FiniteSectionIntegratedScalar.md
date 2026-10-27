## What changed

Kept the signature and docstring of
`AlgebraicGeometry.Etale.FiniteSmoothPurity.integratedSpecialization_scalar`
unchanged. Its proof now separates the three actual factors of integrated
specialization. The private proved helper `normalSectionMap_scalar` obtains the
cone-to-bundle coefficient square from `section_scalar_base_change`, with the
identity-pullback scalar coherence theorem supplying the two unit comparisons.
The main proof postcomposes with the invertible B bundle adjunct and normal-section
map, applies the two factor squares and this proved cone square, uses both defining
integration equations, and cancels the postcomposition.

Added two modules, one statement per module:
`Sheaf.Paper.FiniteSectionSpecializationScalar` and
`Sheaf.Paper.FiniteBundleSectionAdjointScalar`. The first treats only the normalized
zero-fibre specialization, with a single annihilator; the second treats only the
bundle zero-section adjunct, for an arbitrary vector bundle, with the normalized
root comparison from N to M. Neither restates the composite goal. Their docstrings
and nodes give the complete arguments and sources. The first has no integration or
Tate comparison; the second has no deformation family, ambient smooth section or
cone comparison.

Added four private proof imports to the item: these two new modules,
`Sheaf.SecSmoothPurity.SectionScalarBaseChange`, and
`Sheaf.Paper.EtaleScalarPullbackIdentityNormalization`. The original public imports
and all existing public interfaces are unchanged. Only the item's existing node
and the two new nodes are changed.

## Proved and sorry left

One original hole is closed in the item module:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.integratedSpecialization_scalar`
(node `lem-sp-finite-section-integrated-scalar`). No sorry remains in that module.
The private cone square and the categorical combination proof are complete.

Two holes are added, each as the entire proof of its public named theorem:

- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSectionSpecialization_scalar`
  in `Sheaf.Paper.FiniteSectionSpecializationScalar`, node
  `lem-sp-finite-section-specialization-scalar`.
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteBundleSectionAdjoint_scalar`
  in `Sheaf.Paper.FiniteBundleSectionAdjointScalar`, node
  `lem-sp-finite-bundle-section-adjoint-scalar`.

This is a decomposition, not a proof eliminating the underlying obligation:
one hole closed, two added, net minus one. It isolates two strictly smaller,
independent geometric factors and proves the cone factor and their assembly.
The edge cases checked in the new statements are d=0, N=M, zero coefficient rings,
and the empty base. The specialization statement needs no exponent for B because
its N-annihilation follows from the ring homomorphism.

## No longer needed

No existing import is removed, and no module is withdrawn or claimed globally
unreachable. The three public imports are required by the unchanged statement.
All four new private imports are used by the proof.

The item's former direct proof dependencies on
`lem-pur-finite-section-family-constancy`,
`lem-trf-section-local-dualizing-comparisons`, and
`lem-trf-etale-shifted-line-normalized-descent` now belong to the new specialization
node's proof, so these mathematical obligations remain needed there. Its former
direct dependencies on `lem-pur-vector-trace-scalar-descent` and
`lem-pur-integration-transpose-scalar-mate` now belong to the new bundle-adjunct
node's proof and also remain needed. Their modules are not imported speculatively
by the item. `det-sp-scalar-extension-functor` is removed as a direct proof edge:
this ordinary-etale equation uses the existing ordinary scalar functor and the
normalized `CoefficientLineComparison.tensorPower`, rather than the separate
pro-etale scalar-extension theorem. Its module is not globally pruned.
`lem-pur-section-scalar-base-change` and
`lem-trf-finite-ring-section-deformation` remain direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement correction or dispute. The original plan describes the correct
three-factor argument, but the named dependencies do not directly state its two
missing factor squares in the needed generality. In particular,
`VectorTraceScalar.vectorTraceScalarDescent` has a common exponent and concerns
traces, whereas the needed bundle section-adjunct square changes N to M and uses
the specific root-generator comparison. The existing public
`dncCoefficientTransport` has a finite-field and prime-power setting. Its private
generic transport helper assumes invertibility of scalar section maps; these
hypotheses are not provided in the arbitrary finite-ring setting here. Those
restricted theorems were not applied outside their hypotheses.

The unit's statement and route are preserved. No source-library declaration,
target, shared definition, existing signature, attribute or public import changes.
No forced adaptations or change records are required.

Validation: both new statement modules compile through `lcompile.py`; the item
compiles against them with no warning and no sorry in its proof. The item compile
reported 30.6 seconds. The unchanged public signature and the union of the uses
in each node's proof steps were also checked directly.

## New nodes

`lem-sp-finite-section-specialization-scalar` records precisely the zero-fibre
scalar square obtained from the two Rees fibre squares and rigidity of maps
between pulled-back shifted locally constant sheaves. Its module is
`lean/Sheaf/Paper/FiniteSectionSpecializationScalar.lean`.

`lem-sp-finite-bundle-section-adjoint-scalar` records the coefficient and
annihilator-change square for the integration adjunct restricted to the zero
section of an arbitrary vector bundle. Its proof follows the Kummer power diagram,
ordered affine counits, bundle-frame descent, transposition and section cancellation.
Its module is `lean/Sheaf/Paper/FiniteBundleSectionAdjointScalar.lean`.

Both inherit the item's chapter and unit, retain the blueprint ancestor and route,
and include LeanSearch, LeanFinder and source-grep searches. No change record is
added because all existing interfaces remain unchanged.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
