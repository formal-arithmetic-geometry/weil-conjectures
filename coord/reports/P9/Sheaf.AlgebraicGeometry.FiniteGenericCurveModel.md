## What changed

Proved `AlgebraicGeometry.exists_finite_generic_curve_model` with its original signature,
visibility, universes, public imports and docstring. Three proof imports supply the pre-existing
source generic-model theorem, dimension preservation over field extensions, and the canonical
reduction factorization API. The proof converts the chosen-algebraic-closure dimension bound
into the source theorem's arbitrary-geometric-point bound; identifies its reduced surjective
closed subscheme with the canonical reduction; reindexes its finite coproduct by `Fin n`;
and transports the finite boundary and the restriction isomorphism.

Single-file compilation is the verification. No definitions or consumers are changed.
The mixed Lean attachment records the already existing source formulation on the same blueprint
node. Its construction keeps the original eleven-step plan; four preceding steps document the
proved adapter. This avoids a duplicate node for the same blueprint statement.

## Proved and sorry left

Closed 1 of 1 holes in the item: `AlgebraicGeometry.exists_finite_generic_curve_model`
(node `lem-fin-generic-curve-model`). Zero holes remain in the delivered module. Added zero
Lean holes and split off zero statements.

The existing `AlgebraicGeometry.exists_isFinite_sigmaDesc_genericCurveModel` in
`WeilConjectures.AlgebraicGeometry.Curve.GenericModel` remains `sorry`; it is now explicitly
attached to `lem-fin-generic-curve-model` alongside the adapter. The proof is from that existing
library declaration, as authorized by the shortest-route rule. It does not assert that the
geometric construction is axiom-free or that the closure net has improved by one. Its remaining
work is exactly the retained eleven-step normalization, spreading and boundary construction.

## No longer needed

The following direct proof imports are removed because their geometric construction is already
encapsulated by the existing source theorem, or because they were unused duplicate/re-export
imports:

- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.ComponentIntersectionsFinite`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicGeometry.FinitePushforwardFiniteType`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
- `Sheaf.AlgebraicGeometry.Curve.DenseOpenFiniteComplement`
- `WeilConjectures.AlgebraicGeometry.Curve`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage`
- `Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Sheaf.AlgebraicGeometry.FiniteOverProjective`
- `Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite`
- `Sheaf.AlgebraicGeometry.SpreadFiniteAlgebra`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
- `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback`

These are pruned from this module's direct proof-import list. The underlying construction
lemmas are still part of the source theorem's retained plan, so no DAG node is declared globally
unnecessary. The original public imports are retained to preserve the exposed interface.

## Where the brief, the DAG or earlier work was wrong

The source library already states the same geometric construction in an explicit-projective-
embedding, arbitrary-finite-index formulation. The audit listed its declaration with no node.
The initial item did not use it. The adapter is nontrivial: arbitrary geometric fibres,
iterated pullback versus direct pullback, reduced closed subscheme versus nilradical subscheme,
finite index versus `Fin n`, and restriction versus pullback projection are all converted in Lean.
No mathematical statement is changed and no unit route is bypassed: the reused theorem implements
the same blueprint lemma and retains the normalization/spreading/boundary plan.

Searches were run with LeanFinder, Loogle, LeanSearch, and grep through `msearch.py`.
The semantic Mathlib hits do not provide the model. Repository grep found the exact source
construction theorem, and the whole-blueprint search found only this same blueprint node.
The source statement and the current blueprint statement/proof were read. Small cases checked:
empty family (`Fin 0`), isolated point factors, nonreduced original X, and field-valued points
with transcendental residue-field extensions. The argument uses dimension invariance for any
field extension and reducedness only after the source theorem supplies it.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
