## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.projective_normalized_unit_counit_restriction`
with its entire signature unchanged. Reused the already proved pointwise diagonal tensor
isomorphisms and their naturality to construct the requested natural isomorphism whose
forward components are exactly `diagonalTensorMap`. Used the inverse of `pushSectionIso`
for the second conclusion.

For the last conclusion, reused locally the proved parametric private helper arguments
from `Sheaf.Paper.RationalP1UnitCounit`: naturality of the projection mate in its pushed
variable, twisted projection, diagonal-class insertion, unit and counit composites;
restriction to full subcategories; and uniqueness from component normalization.
They remain private and proved here. Importing that module would not expose its private
helpers and would pull in its specialized rational-coefficient theory. No new public
helper or alternate definition of any mathematical object was introduced.

The two fixed component formulas use precisely the supplied inversion witnesses.
Their proof irrelevance makes normalization determine each component, and natural
transformation extensionality determines the pair. No triangle identities are assumed.
Updated the item's node proof, proof dependencies and proof origin to match this route.
Validation: the standalone server check compiled in 31.3 seconds. Its unused-hypothesis
warnings were addressed by explicitly referencing the retained hypotheses. The delivery
preflight checks the final source again, including its axiom probe.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.RationalP1.projective_normalized_unit_counit_restriction`
(node `lem-sfb-projective-normalized-unit-counit-restriction`).

Holes closed: 1 of 1. Holes added: 0. No `sorry` remains in the delivered module.
No split statements were added.

## No longer needed

Removed these proof imports:

- `Sheaf.Paper.ProEtaleProjectionExchangeMaps`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.AlgebraicGeometry.NoncommutativeRingedOpenClosed`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`

Removed these direct proof dependencies from the item's node:

- `lem-sf-exact-functor-derived-triangulated`
- `lem-sfb-noncommutative-ringed-open-closed`
- `sk-def-sfb-derived-categories`
- `sk-def-sfb-derived-tensor-hom`
- `def-sfb-proetale-projection-exchange-maps`

The first three were planned for repeating the support/localization proof, which is
already encapsulated in the proved diagonal comparison. The tensor-Hom module remains
a public statement import and supplies the ambient structures, but no separate
closed-tensor vanishing argument is needed here. The projection/exchange interface
module is already publicly imported by the diagonal module; none of its separate
trace exchange/projection declarations is used directly in this proof.
Removed the obsolete `tool_uses` approval for
`lem-sfb-noncommutative-ringed-open-closed`, since the new proof does not use it directly.

These are direct-dependency removals only: none is claimed to have become globally
unreachable, and no shared module or declaration is withdrawn. All other imports
and all unit statements and steps are retained.

## Where the brief, the DAG or earlier work was wrong

The DAG planned to reprove the diagonal support argument even though
`RationalP1DiagonalTensor` already proves both invertibility and naturality of the
fixed map. The general restriction/naturality argument also already exists as private
proofs in `RationalP1UnitCounit`; it can be reused locally without its specialized
coefficient assumptions. No statement or definition repair was required.

Searches used the required `msearch.py` LeanFinder, Loogle and grep services, plus
local `rg` over both source roots. Loogle located `NatIso.ofComponents`; the local
search found the existing diagonal results and the private parametric construction.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
