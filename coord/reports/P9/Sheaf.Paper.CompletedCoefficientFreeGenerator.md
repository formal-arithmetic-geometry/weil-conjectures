## What changed

Replaced the hole in `completedFreeCell_automaticLinearity` by a sectionwise proof.
For each exponent, a local expression r=a+l^(n+1)b gives an explicit divisibility
witness for the additive action defect. Adic separation then kills that defect.
The statement and every existing definition remain unchanged.

Added `Sheaf.Paper.CompletedCoefficientLocalIntegers`, with the actual approximation
sieve and a proof from the normalized coefficient comparison and the existing
cokernel calculation for `purZlReduction`. A private proved helper extracts local
preimages in a cokernel sequence of abelian sheaves. The new proved module
`Sheaf.Paper.LocalAdicLinearity` contains the general sectionwise action-defect
criterion; the item applies it to the explicit free cell. Local irreducibility
keeps that cell folded while Lean infers the scalar actions, with an explicit
conversion when applying the separation theorem.

Validation: all four modules compile through `lcompile.py` with the normal
60-second Lean limit. The original automatic-linearity signature, all four
existing construction bodies, and `completedFreeDesc_generator` were compared
with the current repository and are unchanged. No shared module was edited.

Added `Sheaf.Paper.CompletedFreeAdicSeparation`, isolating precisely the target-only
separation assertion in step 2 of the original node. This assertion has neither a
source module nor an additive map nor a coefficient isomorphism, so it is strictly
a part of the argument rather than a repackaging of automatic linearity.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedFreeCell_automaticLinearity`.
Its combination proof uses the separation statement below.

Proved
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficient_localIntegers`
(node `lem-sfb-completed-coefficient-local-integers`).
Also proved `CategoryTheory.linearity_of_localIntegers_adicSeparated`
(node `lem-sfb-local-adic-linearity`), with arbitrary ring sheaves and explicit
local approximation and separation hypotheses.
The previously proved `completedFreeDesc_generator` is retained.

Added one hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedFree_adicSeparated`
(node `lem-sfb-completed-free-adic-separation`). Its proof is exactly `by sorry`.
There are no holes in the item module or the local-integer module, and no holes in
any definition. The general criterion module also contains no holes.
This is a decomposition: one original hole closed, one strictly
smaller hole added; no net hole reduction is claimed.

## No longer needed

No existing public imports were removed, and no module is withdrawn. The original
abstract `CategoryTheory.Mod.act_comp_eq_of_epi` criterion is unnecessary for this
proof: the elementary sectionwise action-defect calculation replaces the tensor
and module-object transport. No direct import of that source module is required.

The original direct proof dependencies
`lem-pur-condensed-zl-reduction-mod-ell-power`,
`lem-diagonal-completed-coefficient-ring-comparison`, and
`det-pe-replete-epimorphism` move to the two narrower steps. They remain needed
transitively; none is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The existing declared dependencies do not themselves assert adic separation of a
sheafified free representable. The finite-free separation result in
`PadicIntSheafLinear` has a different target. This delivery implements the actual
coefficient approximation and action-defect calculation, leaving just that
specific separation step. It does not assert a global lift of locally divisible
sections. The new statements include exponent one, zero sections, and empty test
objects. No statement repair or shared-interface change was necessary.

## New nodes

`lem-sfb-completed-coefficient-local-integers`: the covering sieve of integer
approximations of a reconstructed coefficient section. This is proved using the
existing quotient calculation and normalized coefficient comparison.

`lem-sfb-completed-free-adic-separation`: a section of the explicit sheafified free
representable whose positive-power image sieves are all covering is zero. This is
the single remaining hole and the separation step of the original node.

`lem-sfb-local-adic-linearity`: the general local approximation/separated-target
criterion, proved by an explicit divisibility witness for the action defect.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
