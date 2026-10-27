## What changed

Decomposed the remaining `finiteGeometricPurityMate` obligation along the actual
two factors of smooth purity. The original statement, including invertibility of
B at GM and the literal inverse-purity formula, is unchanged.

The existing support API is extracted to `FiniteGeometricPurityCoordinates` and
publicly reexported. Its definitions and existing public signatures are unchanged.
Three existing, fully proved etale-origin helpers are newly public. Four proved
private structural-map independence lemmas avoid large specialized definitional
equality checks in the retagging theorem. The original
public imports remain available through the coordinate reexport.

`FiniteGeometricPurityFactors` constructs the orientation factor, the tensor
transpose in any given etale presentation, the tensor/pullback square, and the
canonical dualizing exchange at the coefficient unit. The latter uses ordinary
exceptional base change and the canonical unit pullback; it is independent of Pi
and Gamma. Its factorization theorem follows from the existing normalized tensor
map's presentation equation.

The assembly chooses etale representatives only inside a theorem proof, applies
the two independent factor identities, proves B invertible using etale origin of
GM, and cancels the pulled-back existing purity isomorphism. No definition chooses
an arbitrary representative or an unnormalized endpoint isomorphism.

Change record: `coord/changes/P3-finite-geometric-purity-factorization.md`.

## Proved and sorry left

Original holes closed: `WeilConjectures.PurityFiniteSetting.finiteGeometricPurityMate`.
This is a decomposition, not a complete proof from sorry-free dependencies: one
original hole is replaced by two strictly smaller geometric obligations (net -1).
The original item module contains zero sorry after the change.

New proved theorem: `WeilConjectures.PurityFiniteSetting.geometricPurityMap_factors`.
All extracted existing support proofs remain complete. The retagging proof uses
proved generic independence lemmas; its statement is unchanged.

New holes, and the only sorries in this delivery:

- `WeilConjectures.PurityFiniteSetting.geometricPurityOrientation_exchange`, node
  `lem-pur-finite-geometric-orientation-exchange`, in
  `Sheaf.Paper.FiniteGeometricOrientationExchange`.
- `WeilConjectures.PurityFiniteSetting.geometricPurityTensor_exchange`, node
  `lem-pur-finite-geometric-tensor-exchange`, in
  `Sheaf.Paper.FiniteGeometricTensorExchange`.

The first is an identity for inverse Pi tensored with an arbitrary input, with no
theta. The second is the tensor-counit identity and has no relative dimension,
Pi, Tate shift or primitive root. Their actual shared intermediate tensor object
and canonical unit exchange make the combination a Lean calculation, not an
application of the original theorem under a different name. Each hole has a
source, full proof in words, its own module, and a matching node.

## No longer needed

No module is withdrawn, and no mathematical dependency is globally pruned.
The original proof imports move with the support proofs that use them; they are
not removed from the dependency closure. The item now directly imports only its
public coordinate API and its two factor exchange proof modules. The six
private proof imports moved intact to the coordinate file are
`Sheaf.Paper.FiniteRootLinePowerTransition`,
`Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`,
`Sheaf.Paper.FiniteCoefficientSmoothPurity`, `Sheaf.Paper.PullbackTorAmplitude`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, and
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`. None is globally pruned.

The parent's old direct generic-tool approvals are removed from its top-level
`tool_uses`: Frobenius-square Cartesianity, uniqueness of right adjoints, purity
base-change factors, roots-of-unity inverse image, pro-etale inverse image along
isomorphisms, finite smooth purity, and extension-integers DVR. Their mathematical
roles remain in the appropriate lower coordinate or factor nodes, rather than
being claimed as direct uses by the categorical assembly. In particular no
finite-ring orientation, root normalization, tensor transpose, counit equation,
finite-coefficient purity theorem or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing declaration `finite_factors` has canonical pullback schemes and
ordinary-etale presentation coordinates; it is not directly the self-square
formula in the assigned fixed-scalar module. The remaining obligations are these
coordinate and factor comparisons. The support results for the normalized source,
input domain, compact-support invertibility and unique counit mate were already
proved; they are retained, rather than split again.

The rework row records a quarantined import failure from the earlier build.
The current item source is present and its initial compile succeeds; neither the
quarantine archive nor its dependencies are deleted or treated as withdrawn.
No statement is weakened, no source-library declaration is altered, and no
second reader is claimed. The original theorem signature is byte-identical.

Validation: the factor API, orientation obligation, tensor obligation and assembly
compile in 5.3 s, 4.1 s, 4.1 s and 5.8 s respectively. The support file
compiles without profiling options in 54.1 s. All five files are below the
60-second limit; the delivery tool performs the final packet and axiom checks.

## New nodes

`def-pur-finite-geometric-purity-coordinates`: the extracted fixed-scalar source,
compact-support exchange, geometric input and uniquely normalized counit-mate API,
with all of its existing proofs preserved.

`lem-pur-finite-geometric-purity-factorization`: the concrete inverse-orientation
and tensor-transpose factors, tensor square, unit dualizing exchange, and the
proved factorization of the specified Gamma in every etale presentation.

`lem-pur-finite-geometric-orientation-exchange`: base change of the inverse
orientation factor, including the specified gamma(zeta) root normalization.

`lem-pur-finite-geometric-tensor-exchange`: base change of the tensor transpose,
using the actual compact-support counit mate and its ordinary unit component.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
