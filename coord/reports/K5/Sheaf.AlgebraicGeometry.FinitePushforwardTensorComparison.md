## What changed

Filled `AlgebraicGeometry.Etale.finitePushforward_tensorComparison` in
`Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` without changing its statement,
its four data definitions, or any public import. Private proved lemmas carry out the
successive adjunction transposes, exchange counit identity, tensor naturality, and unitor
calculation for arbitrary bifunctors between abstract categories. The specialization uses the existing
canonical derived exchange and projection maps, so the equality concerns the specified
arrows, not merely isomorphic objects.

Finite exactness and exchange are already available for the coefficient category itself.
The exact-derived factorization promotes finite exchange to unbounded derived exchange;
the proper torsion projection formula gives the two reduction isomorphisms. The final
implication is cancellation of these isomorphisms. Updated the item's DAG proof and
proof dependencies to this route. No new module, public declaration, definition repair,
forced adaptation, or new node is included.
The additional section variables and local elaboration attributes are documented in
`coord/changes/finite-pushforward-tensor-comparison-proof-context.md`; all new helpers
are private, and these commands do not export any added assumption or global attribute.
Remote single-file validation passed without diagnostics in 31.6 seconds.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.finitePushforward_tensorComparison`
(node `lem-kun-0f1j-finite-pushforward-comparison`). All private helper theorems are proved.
Added holes: zero. Remaining holes in the delivered module: zero. No split-off theorem.

## No longer needed

Removed proof imports:

- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`

The basic adjunction, square and tensor-comparison imports are supplied by imports the
proof actually uses. The direct coefficient-valued finite APIs avoid the separate
coefficient-forgetting and exactness bridge modules. The target reduction is defined
using a conjugate of composite adjunctions, so its compatibility follows directly from
the conjugate counit identity; no K-injective composition comparison is required.

Removed direct proof dependencies:

- `def-weil-pbc-direct-image`
- `def-weil-pbc-underived-exchange`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `prop-weil-pbc-inverse-image-modules-exact`

The seven obsolete top-level `tool_uses` approvals for exact-derived comparison,
coefficient forgetting, inverse-image composition/module exactness, module colimits,
K-injective preservation, and ringed-topos pushforward composition were removed in their
original relative order. The four retained approvals cover finite permanence,
finite properness, finite exactness and finite exchange.

No source-library declaration or module was deleted. These are removed direct edges
from this item's proof; some nodes remain reachable through other statements or proofs.

## Where the brief, the DAG or earlier work was wrong

The original plan's detour through underlying abelian sheaves and a general ringed-topos
composition theorem is unnecessary for the existing Lean definitions. Finite exactness
and finite exchange already support these coefficient categories, and the specified
composition arrow is already the conjugate of the square inverse-image isomorphism.
The closed source APIs `derivedSquareUpperStarIso_hom_tensor` and
`leftDerivedUpperStarTensorComparison_leftUnitor_hom` supply the coherence used by the
formal transpose calculation. This preserves the finite-pushforward route of the unit.

Directly unfolding the concrete derived monoidal constructions during rewrites was
expensive. The proof instead isolates the formal calculation over abstract categories
with bifunctors and comparison natural transformations. The final specialization spells out
the coefficient category instead of introducing local category aliases, keeping instance
choices aligned with the original statement. No mathematical statement was weakened.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
