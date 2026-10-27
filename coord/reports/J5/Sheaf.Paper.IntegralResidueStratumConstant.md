## What changed

Filled the original proof of
`AlgebraicGeometry.Scheme.integralResidueStratum_constant` without changing its
signature or its public imports. The proof constructs the coefficient-universe
lift of a bounded finite-projective representative and proves that its terms
remain finite projective. It then applies an ordinary module comparison and the
K-flat computation of the specified derived scalar extension.

Added two supporting modules, both with complete proofs:
`Sheaf.Paper.IntegralResidueStratumOrdinary` and
`Sheaf.Paper.IntegralResidueStratumScalar`. The ordinary comparison is proved by
explicit constant-presheaf/evaluation adjunctions at a terminal pro-etale object.
Its two right adjoints have the same underlying sections, and scalar
normalization identifies their module actions. The scalar equation is proved
from the finite projection normalizations of `purCoefficientIso`,
`integralCoefficientULift`, and the supplied coefficient model's
`completed_projection` and `finite_constants`. Joint monicity of limit
projections gives equality before projecting. The generic scalar inverse-image
identity then transports it along the arbitrary morphism g.

All new definitions are private, explicit constructions without holes. The
local irreducibility attributes protect the existing completed realization
functors from unnecessary unfolding during the comparison proofs; they do not
change any imported interface. Existing source-library files are untouched.

Compiled all three modules together through `lcompile.py` with zero Lean errors.
The final timing profile measured 45.2 seconds for scalar normalization,
48.2 seconds for the ordinary comparison, and 49.0 seconds for the main module.
Profiling options were then removed before delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.integralResidueStratum_constant`.

New supporting theorems are proved:
`AlgebraicGeometry.Scheme.integralResidueStratum_ordinary`
(node `lem-weil-pbc-integral-residue-stratum-ordinary`) and
`AlgebraicGeometry.Scheme.integralResidueStratum_scalar`
(node `lem-weil-pbc-integral-residue-stratum-scalar`).

Holes closed: 1. Holes added: 0. No `sorry` remains in any delivered module,
and no definitions contain proof holes. No claim is made that unrelated
statements imported through the existing library have all been proved.

## No longer needed

No original import was removed: the assigned module originally had only its
public statement import `Sheaf.Paper.IntegralResidueStratumInput`.

The proof no longer needs the original direct proof-dependency nodes
`def-weil-l-adic-coefficient-extension` (the algebraic universe transport does
not need finite-extension finiteness lemmas),
`lem-weil-pbc-completed-realization-derived-cohomology` (its homology and shift
API is unnecessary; use the localization factorization itself), or
`def-weil-pbc-ringed-derived-restriction` (no localized-site restriction occurs).
The ordinary comparison uses evaluation adjunctions, rather than a separate
geometric constant-module comparison or scalar/inverse-image interchange theorem.
`lem-weil-pbc-completed-constant-sheaf-reduction` is not needed directly for that
ordinary comparison; its flatness content remains behind the existing exact
integral realization API. These removals are changes to this proof route, not
withdrawals of existing shared modules. No existing module is withdrawn and no
unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old final proof step refers simply to deriving exact functors. The right
side uses `completedAdicDerivedChange`, a specified left derived functor whose
ordinary scalar extension need not be exact. The proof now supplies the
missing justification: the bounded-above constant complex has flat terms,
hence is K-flat, and the specified derived counit is invertible there.

The library contains an evaluation-adjunction argument in the later module
`ExtensionZeroPerfectModelTransport`, but that module already reaches this
item, so importing it would create a cycle. The needed elementary adjunction
construction is written locally with proved private helpers instead. No
existing declaration or target statement is weakened or changed.

## New nodes

`lem-weil-pbc-integral-residue-stratum-ordinary` records the natural isomorphism
of ordinary module realization functors. Its proof is the terminal evaluation
adjunction argument and the scalar equation; it has no complexes or perfectness
hypotheses and is fully proved in its new module.

`lem-weil-pbc-integral-residue-stratum-scalar` records the equality of the two
normalized constant scalar sections. Its proof uses finite projections and
constant-section normalization, followed by the inverse-image adjunction unit.
It is fully proved in its new module. Both nodes belong to the assigned node's
chapter and unit and cite the same integral-lattice step of Bhatt--Scholze,
Lemma 6.5.8(1) and Proposition 6.6.11. No change record is needed: only the
assigned module/node and these new modules/nodes are changed.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
