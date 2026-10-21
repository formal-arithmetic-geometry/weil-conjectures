## What changed

Filled the five theorem proofs in
`Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization`, preserving all
existing statements and definitions. The open proof uses the normalized cochain
mate comparison to localize the existing ordinary unit equation, then applies the
unit and counit equations for mates. The closed proof uses finite etale direct-image
exactness, the quasi-compact complementary open on the pro-etale side, and the
universal factorization of the canonical bounded-below right-derived comparison.
Proved private helpers supply the exact Hom and square factorization calculations,
localization of the inverse mate, invertibility of localized units, and the exact
right-derived base-change and counit calculations.

Added private proof imports of the finite etale exactness module, both ordinary
open full-faithfulness modules, the etale closed full-faithfulness module, the
normalized derived mate module, and the exact-square helper API. Existing public
imports remain unchanged.

The source read was the second paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`.
The node proof and dependency list now describe this argument. No target, public
signature, definition body, or source-library file changes.

Validation: the complete item module compiled through `lcompile.py` in 8.2 seconds
with exit code 0. A textual comparison confirms all 12 original declaration
signatures remain unchanged; all Lean lines fit within 100 characters.

## Proved and sorry left

Closed all five original holes, with no holes added or split off:

- `AlgebraicGeometry.ProEtale.derivedImmersionOpen_normalization`.
- `AlgebraicGeometry.ProEtale.derivedImmersionClosedEtale_exact`.
- `AlgebraicGeometry.ProEtale.derivedImmersionClosedProEtale_exact`.
- `AlgebraicGeometry.ProEtale.derivedImmersionClosed_sheaf_transpose`.
- `AlgebraicGeometry.ProEtale.derivedImmersionClosed_normalization`.

All five belong to `lem-sf-derived-immersion-comparison-normalization`.
No `sorry` remains in the module source. This is a proof from existing library
and Mathlib declarations, not a decomposition into newly assumed statements.

## No longer needed

Removed proof-only imports (their declared intrinsic-coefficient or general-purpose
results are not needed for the fixed-coefficient proof):

- `Sheaf.Paper.ComparisonPullbackExact`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`.
- `WeilConjectures.SixFunctors.OpenClosed.Complex` (use the direct ordinary open
  full-faithfulness module).
- `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` (use the canonical source-library
  right-derived exact-factorization API already in the public imports).
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.

Removed the following redundant proof-dependency edges from this node:

- `def-weil-pbc-extension-by-zero` and `lem-weil-pbc-comparison-pullback`
  remain statement dependencies; their definitions are already available.
- `lem-sf-comparison-pullback-exact`, `prop-weil-pbc-inverse-image-modules-exact`,
  `def-weil-pbc-proetale-operations`, `prop-weil-pbc-proetale-constant-ring-map`,
  `lem-weil-pbc-extension-by-zero-exact`, `lem-weil-extension-by-zero-exact`, and
  `lem-weil-extension-by-zero-adjunction`: the fixed-coefficient functor instances
  and adjunctions are already provided by the canonical definitions' imports.
- `lem-sp-exact-derived-transformation-pasting`,
  `lem-weil-pbc-exact-functor-derived-functor`, and
  `lem-pc-pre-derived-adjoint-functors-general`: replaced by the normalized
  cochain mate comparison and the canonical right-derived factorization equations.
- `lem-trf-oriented-closed-base-localization`: replaced by finite etale exactness.
- `lem-pc-separated-quasi-separated` and
  `lem-weil-pbc-universally-closed-quasi-compact`: standard scheme instances already
  establish these properties of the closed immersion.

No module is withdrawn; this report makes no claim that these declarations are
unused by other project consumers. The statement dependencies remain unchanged.

The detailed fraction-diagram route through
`lem-pc-pre-derived-adjoint-functors-general` is unnecessary: the existing normalized
cochain mate theorem and canonical right-derived factorization equations provide the
actual maps and their equalities. The general closed-complement module transport of
`lem-trf-oriented-closed-base-localization` is unnecessary for etale exactness:
a closed immersion is finite, and the library already proves finite direct-image
exactness for the exact coefficient category used here. The ordinary etale counit
is invertible by its existing fully faithful closed direct-image instance.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The original plan overlooked the
available finite etale exactness theorem and required more general pre-derived
fraction arguments than these exact functors need. The proof works uniformly with
zero coefficients, empty immersions, and identity immersions: it uses only natural
adjunction identities, isomorphism cancellation, and complement exactness, with no
nonemptiness or nonzero-ring hypotheses.

Change record: `coord/changes/d5-derived-immersion-normalization-proof-commands.md`.
It records the elaboration commands and local helper context detected by preflight.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
