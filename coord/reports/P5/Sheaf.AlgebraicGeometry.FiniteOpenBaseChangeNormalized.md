## What changed

Proved both holes in `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`.
`singleBetaInvApp_naturality` uses the open-adjunction Hom-equivalence square,
naturality of the open unit, and naturality of `moduleSquareG.inv`.

For `singleBetaInv_isIso`, the identity scalar map identifies the intrinsic
constant ring with the finite coefficient ring: both constant-unit maps are
locally bijective. The existing realization `C B X B (RingHom.id B)` is therefore
an equivalence. Its existing direct-image comparison identifies pullback by
adjoint uniqueness; a second application identifies open extension. The ordinary
weakly-etale base-change theorem, conjugated under the composite adjunctions,
then proves that the pulled-back extension lies in the open essential image.
The ordinary localization adjoint triple proves full faithfulness of open
extension, which transports through `C`. Thus the module open unit and the counit
at that essential-image object are invertible. The original `singleBetaInvApp`
is the extension of its displayed transpose followed by that counit, so all of
its factors are invertible. The public map is unchanged.

Added proof-only imports of `FiniteConstantCoefficientTransport` (including its
private scalar-unit equations), `ProEtaleOperations` (its constructed scalar
transport equivalence), and the existing source-library `BaseChange.WeaklyEtale`.
All helpers are private and fully proved. Every existing public signature,
definition body, visibility, public import, and docstring is retained.
The helper section's variable and local instance commands are documented in
`coord/changes/P5-finite-open-base-change-proof-scope.md`; they export no new
instance and require no consumer adaptations.

The common blueprint node `lem-cbc-proetale-extension-zero-base-change` retains
its ordinary proof and gains the explicit constant-ring coordinate refinement
and its three existing dependency nodes. No unit statement or route is changed.

Validation: the completed module compiles through `lcompile.py` without warnings.
The proof covers the empty open, empty schemes, identity maps, zero coefficient
ring, and disconnected schemes: no nonemptiness, nonzero-ring, properness,
boundedness or constructibility assumption is introduced. The temporary discrete
topology is local to the proof of invertibility.

## Proved and sorry left

Closed 2 original holes:
- `AlgebraicGeometry.ProEtale.StrictTower.singleBetaInvApp_naturality`.
- `AlgebraicGeometry.ProEtale.StrictTower.singleBetaInv_isIso`.

Both belong to `lem-cbc-proetale-extension-zero-base-change`.
No sorry remains in the item; no holes or axioms were added. This is a proof,
not a decomposition. Existing dependency holes remain with their original owners.

## No longer needed

No imports or modules withdrawn. The original public imports remain part of the
module interface. The underlying right-adjoint comparison is supplied by the
existing `ProEtale.isIso_baseChangeMap_of_isPullback`, rather than reconstructed
from the general ringed-site localization theorem. The existing shared blueprint
node also represents the ordinary interface, so its dependency route is retained;
no whole DAG node is declared obsolete by this coordinate refinement.

No comparison-normalization coherence lemma is needed for the object-level
transport: full faithfulness and the counit formula prove invertibility of the
original canonical transpose directly. In particular there is no dependency on
`StrictTowerProperOpenArrows.betaInv_isIso` or
`VaryingRingProperOpenArrows.moduleBetaInv_isIso` (both would create cycles).

## Where the brief, the DAG or earlier work was wrong

The item has two proof holes, while the only node with this exact `lean.module`
attachment is the already proved square-compositor specification. The two holes
cite the common base-change node in their docstrings; that node's main Lean
attachment is now the ordinary fixed-scalar derived interface. The delivery
preserves that attachment and adds the proof of the constant-ring refinement to
its proof steps. No definition or statement repair was necessary.

The source library already proves the ordinary weakly-etale base-change theorem;
using it and the existing scalar transport avoids rebuilding the site comparison.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
