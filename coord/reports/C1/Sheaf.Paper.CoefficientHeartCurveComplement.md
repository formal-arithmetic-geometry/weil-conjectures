## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_curve_complement` in
`Sheaf.Paper.CoefficientHeartCurveComplement`, with its signature unchanged.
The existing specialization dimension-decrease theorem proves that the complement
has dimension at most zero. The closed-subset finiteness theorem and the
closed-immersion embedding give finiteness and closed points on X.

Repaired the return at db4455834: removed all four duplicate private theorems
`CondensedRing.moduleCounitOfAbelian`, `CondensedRing.moduleUnitOfAbelian`,
`CondensedRing.openRestrictionPushforwardZero` and `CondensedRing.openUnitIsIso`.
The proof now reuses their existing proved declarations through the proof-only
`import all Sheaf.Paper.CondensedOpenClosedRecollement`. No declaration in that
module, FormalClosedSupportSheaves or the adopted source library is changed.

Complementary exact restrictions detect isomorphisms by kernels and cokernels,
then detect short exactness. The triangle identities prove both restricted
sequences short exact. No definition, public signature or public import changed.
Updated the node proof, proof dependencies and proof origin to this argument.
The change record is
`coord/changes/coefficient-heart-curve-complement-proof-helpers.md`.
The downstream checker reports no consumers requiring adaptation.

The import-direction check accepts the shared recollement import. Edge cases
include empty X, empty U, empty complement, reducible or nonreduced X and the zero
module; no extra assumptions are used. The repaired module compiled successfully
through lcompile.py in 4.4 seconds, with no Lean errors or warnings. Delivery
preflight checks the final packet.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.coefficientHeart_curve_complement`
(node `lem-sfb-coefficient-heart-curve-complement`).
Added 0 holes; split off 0 holes. No sorry remains in any delivered Lean file.
All four reused private helper declarations already have complete proofs in the
library; no new local helpers are declared. Imported statements and instances
retain their existing proof status.

## No longer needed

Removed original private imports:

- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.
- `Sheaf.CategoryTheory.SheafTensor`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafClosedLocalization`.

Removed direct imports from the returned packet:

- `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport` and
  `Sheaf.Paper.ProfinitePointPullback`: accessible through the shared proof import.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement`:
  the duplicate vanishing helper is removed.

The direct proof does not use these planned dependencies:

- `lem-weil-pbc-reduced-induced-closed-subscheme`: the given closed immersion
  and image suffice; no construction or uniqueness theorem is needed. It remains
  a statement dependency and its public import is preserved.
- `lem-sfb-noetherian-space-compact-subsets` and
  `lem-weil-pbc-locally-noetherian-quasi-separated`: the direct proof does not
  invoke a qcqs ring-sheaf localization theorem.
- `sk-def-sfb-pulled-back-coefficients`: no additional proof theorem is used;
  its definitions remain statement dependencies.
- `sk-def-sfb-coefficient-morphisms`, `sk-def-sfb-change-of-scalars` and
  `def-sfb-module-linear-open-lower-shriek`: scalar transport is encapsulated
  in the existing imported support helpers, rather than repeated locally.
- `sk-def-sfb-sheaf-tensor` and `lem-sfb-proetale-sheaves-grothendieck`: no
  direct application; use the existing operation and support APIs instead.
- `def-sf-proetale-ring-sheaf-operations` and
  `lem-sf-ring-sheaf-closed-localization`: prove short exactness on actual
  coefficient modules by complementary restrictions.

Removed the obsolete top-level tool_uses approvals for
`lem-sf-ring-sheaf-closed-localization` and
`lem-sfb-proetale-sheaves-grothendieck`; retained the zero-dimensional finiteness tool.
No declaration or module is withdrawn. These removals are local to this proof;
shared imports and other consumers can still need these modules. No global module
pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned packet copied four already-proved private support lemmas. A proof-only
`import all` reuses them directly, as other library consumers already do. The
repair removes every copy named by the return, including the vanishing lemma
whose copied proof had been shortened through the abelian API.

The DAG's comparison of two full localization sequences is unnecessary.
Existing module-support helpers, the module-forgetful pullback comparison and
exact-functor detection give a shorter proof. Dimension decrease is also already
available. The coefficient-heart unit route and every mathematical statement stay.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
