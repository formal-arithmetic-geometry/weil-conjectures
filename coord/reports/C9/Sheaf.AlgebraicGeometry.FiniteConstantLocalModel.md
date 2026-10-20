## What changed

Proved all eight original holes in `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
Every existing public signature, definition and public import is preserved. All
added helpers are private and proved, in the same module.

The scalar interface uses the constant-sheaf adjunction, its monoidal counit and
`constantSchemeIso`. Regular-module and finite-biproduct comparisons identify the
actual scalar matrices. Preservation of cokernels proves both presentation
comparisons on the same cover. Transport of finite presentations proves local
finite presentation.

The counterexample uses continuous 2-adic coefficients on `Spec LC(S,Q)`, where
`S` is a convergent sequence with its limit. Multiplication by `t(n) = 2^n`,
`t(infinity) = 0` has a finitely presented cokernel. Scalar models over this field
are finite free. Geometric evaluation gives cokernel dimension zero at finite
points and one at infinity. A finite affine refinement of a pro-etale cover would
make that dimension locally constant, contradicting density of the finite points.
The proof treats universe lifts, zero ranks and empty covering members.

Private irreducible pullback comparisons and generic rank lemmas avoid repeatedly
unfolding transported monoidal structures. The final module compiles without diagnostics in 26.0 seconds. The delivery
dry run passed compilation, interface and axiom preflight checks (review class CODEX). The existing DAG node now describes the actual proof. The change
record is `coord/changes/finite-constant-local-model-private-helpers.md`.

## Proved and sorry left

Closed all eight original holes, by declaration name:

- `AlgebraicGeometry.ProEtale.scalarRingObj_comm`.
- `AlgebraicGeometry.ProEtale.scalarConstant_iso_constantSheaf`.
- `AlgebraicGeometry.ProEtale.scalarCoefficientHom_isMonHom`.
- `AlgebraicGeometry.ProEtale.scalarConstant_comm`.
- `AlgebraicGeometry.ProEtale.finiteConstantLocalModelOnCover_iff_scalarMatrix`.
- `AlgebraicGeometry.ProEtale.finiteConstantLocalModel_iff_exists_cover`.
- `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel.isLocallyFinitelyPresented`.
- `AlgebraicGeometry.ProEtale.not_locallyFinitelyPresented_implies_finiteConstantLocalModel`.

All belong to `det-def-sfb-constructible-local-model`. Remaining holes in the item:
zero. Added holes: zero. Split-off statements: zero. Existing imported statements
remain separate project items; no claim is made to have proved their holes.

## No longer needed

Removed these original proof-only imports:

- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`.
- `Sheaf.CategoryTheory.SheafTensor`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `Mathlib.AlgebraicGeometry.ResidueField`.
- `Mathlib.AlgebraicGeometry.Limits`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`.
- `Sheaf.Paper.CondensedPointCoefficients`.
- `Sheaf.Topology.ProfiniteCondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

The proof uses the published module-object categories and canonical pullbacks
without the first three separate specifications. Algebraic-closure, residue-field,
limit and module-object infrastructure is available through retained dependencies.
The continuous realization replaces coefficient localization and profinite
point-coefficient comparisons. The extra proof import
`Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars`, considered during the
proof, is also unnecessary: conjugation is checked directly from the evaluation
functor and geometric scalar naturality.

Removed from this node's proof dependencies:
`def-sfb-profinite-test-objects`, `def-weil-geometric-point`,
`det-pe-condensed-point-coefficients`, `lem-sfb-coefficient-sections-localization`,
`lem-weil-pbc-finite-affine-coproduct-spectrum`,
`lem-weil-pbc-spec-small-colimit-limit`, `sk-def-sfb-condensed-ring`,
`sk-def-sfb-pullback-from-point`, `sk-def-sfb-sheaf-tensor`, and
`def-weil-sheaf-of-modules-category`. Their separate specifications or longer
counterexample route are unused. No existing node is retired. Withdrawn obsolete
`tool_uses` approval: `det-pe-condensed-point-coefficients`.

The proof-only dependencies added for regular extension, continuous realization,
internal modules and geometric evaluation are used as tools. The unit's
constant-model and finite-presentation steps are preserved. No maintainer tool-use
approval is added.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had implemented the final counterexample without a successful
full compile or delivery. This continuation repaired the elaboration and kernel
checking of its transported monoidal structures and completed verification.

The original counterexample plan used an algebraically closed base field and
profinite test-object comparisons. The existing continuous realization permits the
same covering contradiction over the rational field. Algebraic closures are needed
only for geometric evaluation. The final theorem's proof docstring now records
this implemented argument. No mathematical statement or existing definition changes.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
