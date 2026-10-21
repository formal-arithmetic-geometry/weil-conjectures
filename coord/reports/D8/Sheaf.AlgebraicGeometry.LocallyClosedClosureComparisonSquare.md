## What changed

Replaced the five theorem proofs in
`Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare`. The main argument
pastes the specified open-unit and closed-counit equations through the canonical
pullback compositor, then detects the closure square after restriction.
Private proved helpers implement the localization and adjunction calculations.
The change square and all identity/cocycle equations use inverse cancellation.
All existing declaration signatures and construction bodies are preserved.

The change record is
`coord/changes/D8-locally-closed-closure-square-proof.md`.
Updated the node proof to describe the Lean argument. The open-unit calculation
reuses the argument of the existing `OpenSiteEvaluationCounit` private helpers,
specialized to the comparison defined in this module; that large consumer module
is not imported. Proof imports supply the existing normalization and exact-derived
square composition declarations.

## Proved and sorry left

Original holes (5):

- `AlgebraicGeometry.ProEtale.locallyClosed_closure_comparison_square`.
- `AlgebraicGeometry.ProEtale.locallyClosed_closure_comparison_change`.
- `AlgebraicGeometry.ProEtale.locallyClosed_closure_comparison_etale_laws`.
- `AlgebraicGeometry.ProEtale.locallyClosed_closure_comparison_proetale_laws`.
- `AlgebraicGeometry.ProEtale.locallyClosed_closure_comparison_termwise_laws`.

Closed all five original holes listed above. Holes added: none. Holes left: none.
Split off: zero. This is a proof from existing declared dependencies, not a decomposition.
The complete module compiled on the project server via `lcompile.py` in 17.5 seconds;
then two unused simp arguments were removed before the delivery compile.
All original declaration signatures were compared with the current source and match
exactly. No `sorry`, axiom, or forbidden implementation declaration occurs in the file.

## No longer needed

The proof does not reconstruct the given normalized `qe` and `qp`, so it does not
use `lem-sfb-etale-locally-closed-extension-comparison`. The restriction-injectivity
argument is proved directly from the open and closed adjunction triangle identities,
so it does not use `lem-sfb-locally-closed-extension-coherence`.

No finite-type argument or Noetherianity of the source or closure is required:
`def-weil-finite-type-morphism` and
`lem-weil-pbc-finite-type-over-noetherian` are unused as proof dependencies.
The exact-derived functors already have bounded-below codomains, so no separate
application of `lem-weil-pbc-extension-by-zero-exact` or
`lem-weil-pbc-exact-functor-bounded-below` is needed in this proof.
These statements remain in the library and may have other users.

Removed imports:

- `Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`.
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` (still an indirect
  proof dependency through the existing open-unit normalization).
- `WeilConjectures.SixFunctors.Finite.Exact`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (available through the exact-derived square API).

`SupportComparisonPullbackCoherence` is now a private proof import. A precise
public import of the finite-coefficient `UpperLowerStar.Iso` module supplies the
existing public definition's `upperStarCongr`. No current Lean module imports the
item, so no consumer adaptation is required. The node's semantic statement
dependencies are unchanged; none of these library modules is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Its generic intrinsic-coefficient Hom
bijection is unnecessary for this fixed-coefficient calculation: a right adjoint
detects morphisms between left-adjoint images, and a left adjoint detects morphisms
between right-adjoint images by the triangle identities. Conjugating the open
restriction with its inverse-unit isomorphism gives the required detection for the
closed-then-open extension directly.

The proof uses the actual normalized maps throughout. No hypothesis changes, new
existence choices, target changes, or new nodes are needed. Empty schemes and the
zero coefficient ring use the same formal equations.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
