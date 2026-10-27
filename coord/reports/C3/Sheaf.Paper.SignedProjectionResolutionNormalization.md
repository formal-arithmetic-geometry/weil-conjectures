## What changed

Proved both theorems in `Sheaf.Paper.SignedProjectionResolutionNormalization` without
changing any existing declaration signature, definition, public import, or docstring.
`model_properties` transports the degreewise finite-free retract package through exact
pullback and applies the existing flatness and K-injective total APIs. The canonical
K-injective direct-image comparison supplies both invertible derived units.

`normalization` applies `proEtaleMixedProjectionMate`, cancels the derived comparisons,
and transports the resulting square along `alpha` and `beta` using naturality of the
canonical projection mate. A proved private categorical helper performs this transport.
The two inverse equations follow by localizing the inverse identities for the specified
finite-total map. No chain-map condition on the splittings or bound on `I` was added.

Removed nine unused private proof imports, and updated the existing node's proof,
proof dependencies, proof origin, and obsolete tool-use entry to describe this proof.
Only the item module and its node are changed; no consumer adaptation is required.

## Proved and sorry left

Closed 2 of the original 2 holes, both attached to
`lem-weil-pbc-signed-projection-resolution-normalization`:

- `AlgebraicGeometry.Scheme.SignedProjectionResolution.model_properties`.
- `AlgebraicGeometry.Scheme.SignedProjectionResolution.normalization`.

Zero holes remain in the item. Zero holes were added, zero statements were split off,
and no new public declaration or node was added. This is a proof from the existing
stated dependencies, including their existing proof obligations, rather than a claim
that those dependencies are all axiom-free already.

Validation: the complete item is compiled through `lcompile.py`; the delivery tool
performs the required declaration probes and preflight. The proof treats arbitrary
coefficient differentials, zero coefficients and rank-zero finite free terms uniformly.

## No longer needed

Removed these direct private imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.

The existing projection-arrows API supplies strict-perfect flatness, K-injectivity of
the pulled coefficient total, and invertibility of the finite-total projection map.
The existing pro-etale operations API supplies the K-injective derived comparison.
The mixed-mate theorem supplies the already-normalized localization square.
Consequently this item's proof no longer separately invokes these planned nodes:

- `def-pc-flat-sheaf-modules`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-weil-pbc-split-perfect-tensor-kinjective`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-weil-pbc-kflat-fixed-tensor-triangulated`.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `lem-weil-pbc-right-adjoint-preserves-limits`.

The planned separate applications of
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-fixed-tensor-localization-comparison`, and
`def-pc-tensor-complex-sheaves` are also encapsulated by existing APIs. These remain
statement dependencies where originally recorded. Public imports remain unchanged.
Transitive uses of any removed direct dependency by the retained modules remain needed;
no module is withdrawn and no adopted source declaration is removed.

Removed the obsolete direct tool approval for
`lem-pc-bounded-above-flat-kflat-site` from this node's top-level `tool_uses` list.
The unit's statement and all realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG expanded several arguments
already exposed as proved APIs in `ProjectionFormulaArrows` and
`ProEtaleProjectionFormulaArrows`. Using those existing declarations shortens the proof
and avoids the planned direct split-perfect and total-derived existence arguments.
No definition repair or change record is needed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
