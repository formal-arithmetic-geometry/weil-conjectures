## What changed

Filled `AlgebraicGeometry.Etale.smoothGenericDirectImage` in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne`.
All existing declaration signatures, attributes and public imports are unchanged.
The other three public proofs are unchanged. Added only proved private helpers
and private proof imports.

The proof uses strong induction on an invertible positive annihilator. For
`n = p * m`, the kernel of multiplication by `p` is killed by `p`, and the
cokernel of its inclusion is killed by `m`. Both remain finite locally constant.
The existing killed-sheaf construction supplies prime-field coefficients for
the kernel. Apply the prime-field smooth generic theorem, transport the full
constructibility/exchange property through the canonical coefficient-forgetting
comparisons, and apply induction to the quotient. Intersect the two nonempty
opens and combine the results with the short-exact-sequence distinguished
triangle and the existing two-out-of-three API.

Private helpers supply the coefficient transport and convert the prime theorem's
open-restriction formulation to `HasDirectImageBaseChangeOnPlus` over the original
base. This includes the bounded-below comparisons, factorization of test maps
through the open, and pasting with its étale exchange square. Added private
imports of `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage`,
`WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility`,
`WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift`,
`WeilConjectures.ConstructibleSheaf.OfForget`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.
Updated the item's DAG proof and direct dependencies to this argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.smoothGenericDirectImage`
(node `lem-fin-smooth-generic-direct-image-finite-ring`).
Added zero holes. The item has zero remaining `sorry`; no new modules or public
statements were introduced. The proof uses existing stated dependencies, including
the prime-field smooth generic theorem, rather than reproving their source theory.
This is one hole closed, not a decomposition. The complete proof has passed `lcompile.py` without errors or warnings.
The induction and elementary annihilation identities are private lemmas over an
abstract abelian category to avoid unfolding concrete sheaf constructions.

## No longer needed

No original imports or modules were removed, and no declarations were withdrawn.
The proof does not use the complete bundled
`Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients` theorem: it uses the narrower
source exchange compatibility API and proves the required isomorphism reflection
privately. Thus `lem-weil-pbc-exchange-forget-coefficients` is removed as a direct
proof dependency and tool approval; its relevant source components remain needed.

The explicit prime-factor filtration and separate long-exact-sequence/five-lemma
steps are replaced by annihilator induction and the already proved
`HasDirectImageBaseChangeOnPlus.of_distTriang₂` API. The direct proof dependencies
`lem-sf-derived-homology-long-exact` and
`lemma-weil-pbc-five-lemma-transfer` are no longer needed here. The latter's tool
approval is removed. This does not withdraw these declarations or claim that
other consumers no longer need them. The separately cited definitions
`def-sbc-locally-finite-presentation` and `def-weil-finite-type-morphism` are not
needed as direct proof dependencies: Mathlib's smooth-to-locally-finite-type
instance supplies the geometric hypothesis. The broad coefficient-devissage proof import is also unnecessary: the finite
underlying-sheaf fact is proved privately from the elementary APIs.
All other tool approvals are kept
in their original order.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The prior docstring named only the prime-field
node, whereas the actual finite-ring declaration is attached to
`lem-fin-smooth-generic-direct-image-finite-ring`; the docstring now identifies
that node and explains its finite-ring proof. The DAG plan is mathematically
usable but can be implemented more directly with kernels/coimages and the
existing triangulated closure API. The unit route and target statements are
unchanged.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
