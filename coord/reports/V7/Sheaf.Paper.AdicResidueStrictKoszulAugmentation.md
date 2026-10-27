## What changed

Replaced the proof hole in `AdicResidueStrictKoszulAugmentation` by a reduction to
three independent coefficient-level statements. The original theorem signature,
its hypotheses, and its public imports are unchanged.

`AdicResidueQuotientTensorTower` constructs the restricted quotient coefficient
modules, their actual R-linear successor maps, their single-degree complexes,
and the strict tensor tower and insertion-of-one maps. The successor maps are
constructed sectionwise, not chosen from an existence statement. The equality
of the two composite coefficient projections is proved from the completion
cone. `AdicResidueKoszulCoefficientAugmentation` also proves the comparison
between the adjacent-differential and transposed Koszul tensor models and defines
tensoring of a supplied augmentation. The private generic lemma `limit_map_projection` avoids unfolding the sheaf
constructions in a general limit calculation. The private lemma
`tensor_augmentation_projection` proves the required limit projection equation.
The parent theorem supplies the constructed target and tensor augmentation,
then combines that equation with the scalar-model and cone statements. The new
tensor-augmentation definition is irreducible to prevent accidental expansion
while elaborating mapping cones; its component proof unfolds it explicitly.

The three remaining statements isolate different parts of the source argument:
construction of a coefficient chain map without P or Noetherianity; the derived
cone calculation for a supplied map without constructing a scalar-tower
isomorphism; and identification of the quotient tensor tower with the normalized
scalar-adjoint tower without any Koszul list or cone assertion. None is the
original existential statement under a different name. No existing definition,
interface, target, or source-library module was changed.

## Proved and sorry left

Original holes: 1. Original holes replaced by a complete combining proof: 1,
`AlgebraicGeometry.Scheme.adicResidue_strict_koszul_augmentation`.
New holes: 3. This is a decomposition, not a net proof closure; the net change in
holes in this packet is +2. The item module itself has no remaining sorry.

Every added sorry is a whole named public theorem in its own new module:

- `AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_augmentation`
  (`lem-sfb-adic-residue-koszul-coefficient-augmentation`).
- `AlgebraicGeometry.Scheme.adicResidue_koszul_tensor_cone_proZero`
  (`lem-sfb-adic-residue-koszul-tensor-cone-pro-zero`).
- `AlgebraicGeometry.Scheme.adicResidue_quotient_tensor_model`
  (`lem-sfb-adic-residue-quotient-tensor-model`).

All five sandbox modules compiled together in dependency order; the parent took
38.4 seconds and every other file was below 30 seconds. Delivery rechecks the
final packet after the redundant-import cleanup.

All definitions have explicit bodies. The quotient-projection successor identity,
the Koszul tensor transposition comparison, and the parent limit-projection glue
are proved. Each remaining theorem includes its source, blueprint node, full
proof in words, and the relevant degenerate cases.

## No longer needed

No original public import is removed, and no existing module or node is
withdrawn. The redundant direct import of `Sheaf.Algebra.Homology.KFlat` was
removed from the new quotient-tower module; the needed K-flat predicate remains
available through the existing public dependency chain. This does not prune that
module from the target closure. The direct parent proof no longer needs a separate use of
`lem-pc-kflat-resolution`: P and its K-flatness are already hypotheses. The
algebraic theorem `lem-weil-pbc-noetherian-koszul-augmentation-pro-zero` and the
flatness/quotient facts of
`lem-weil-pbc-constant-completion-equivalence` remain necessary to the cone
subproblem, so they are retained there rather than claimed as pruned. There is
no assertion that the corresponding existing modules can be deleted. The
blueprint unit's statement and realized proof steps remain intact.

## Where the brief, the DAG or earlier work was wrong

The listed algebraic pro-zero theorem concerns ordinary A-module Koszul
complexes, whereas the requested conclusion uses actual complexes of towers of
sheaves on a slice, an internal-Hom dual Koszul model, and a specifically
normalized derived scalar adjunction. Its conclusion cannot directly instantiate
the original existential statement. The intervening constructions and comparison
steps were described in the parent node but lacked matching declarations with
these interfaces. This packet makes the quotient tower and the final combining
argument explicit and states precisely the three outstanding comparisons.
No original mathematical statement is disputed or weakened. The first preflight
returned a metadata-only error: the definition node had included the body in
`lean.statement`. This was corrected to the verbatim signature. LeanSearch was
also run and recorded to complete the three search categories; its hits are
generic ordinary-module and complex constructions, not the missing comparisons.

Edge cases were checked in the new statements: the coefficient construction
allows an empty list and merely containment in J; the cone statement uses equality
with J and hence has J=0 for an empty list; the scalar-model statement needs no
flatness of the quotient. Unit ideals, zero rings and zero complexes satisfy the
same formulas. The Noetherian pro-zero result is still used only where its
hypotheses hold.

## New nodes

`def-sfb-adic-residue-quotient-tensor-tower` records the explicit strict quotient
and tensor constructions and their proved projection compatibility; its module
has zero holes.

`lem-sfb-adic-residue-koszul-coefficient-augmentation` records the degree-zero
augmentation of the coefficient Koszul tower before tensoring. Its module also
contains the proved transposition comparison and actual tensor augmentation.
The negative Koszul duality and signed finite-coordinate declarations supply the
existing interfaces for its basis calculation.

`lem-sfb-adic-residue-koszul-tensor-cone-pro-zero` records the Noetherian
cone-transition calculation for a supplied normalized coefficient augmentation.
Its proof plan uses the existing algebraic pro-zero theorem, the completed
coefficient flatness/quotient theorem, and K-flat tensoring.

`lem-sfb-adic-residue-quotient-tensor-model` records the scalar-adjoint
identification of the fixed quotient tensor tower, including its unit
normalization and successor compatibility. It uses the existing finite scalar
comparison and normalized adjoint-tower interfaces.

The parent node's proof, proof dependencies, and proof origin are updated to the
combining argument. There are no change records because no other existing
module or node, and no existing statement or definition, was changed.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
