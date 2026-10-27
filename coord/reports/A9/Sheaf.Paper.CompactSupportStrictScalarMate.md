## What changed

Proved nine of the module's twenty original obligations, preserving every signature,
public import, and definition body. Added two proved private categorical helpers:
left-adjoint uniqueness transported along a right-adjoint isomorphism, and the
geometric transpose of a scalar mate. The ordinary base-site tensor construction
and its invertibility theorem were moved before their tower application without
changing their statements or definition bodies.

Restriction exactness follows from the existing exact tower restrictions by
constant diagrams and evaluation at zero. Base tensor exactness is obtained the
same way from exact tower tensor. Arithmetic selection reuses the proved
StrictTowerArithmetic.restriction_preservesKInjectives. Transition compatibility
is naturality of the actual whole-diagram transformation. Proper/open pasting
uses Mathlib mateEquiv_vcomp. Both geometric transpose formulas use the proved
private helper and the specified composite adjunctions. Ordinary open tensor
base-site invertibility uses iterated mate/conjugation; it is independent of a
coefficient basis. The separate tower invertibility proof remains unfinished.

Updated the item's proof and dependency records to describe these arguments,
while retaining the mathematical plan for the still-unproved obligations.
No new theorem with sorry, axiom, or data construction was introduced.

## Proved and sorry left

Closed 9 original holes; added 0 holes. This is proof progress, not a decomposition.
All names below are in namespace WeilConjectures.PurStrictScalar and attached to
lem-pur-compact-support-strict-scalar-mate.

Proved:

- `subsequence_preservesKInjective`.
- `ordinaryPositiveRestriction_exact`.
- `ordinaryFiniteRestriction_exact`.
- `baseTensor_exact`.
- `arrow_transition`.
- `strictProper_geometric_transpose`.
- `comparison_pasted`.
- `ordinaryBaseOpenTensor_isIso`.
- `proper_geometric_transpose`.

Unchanged original holes remaining (11):

- `ordinaryOpenTensor_isIso`.
- `evaluationRestriction_existsUnique`.
- `finiteOrdinaryBalancing_existsUnique`.
- `finiteBalancing_existsUnique`.
- `openTensor_ordinary`.
- `factors_isIso`.
- `pulledBasis_existsUnique`.
- `open_base_ordinary`.
- `proper_biproduct`.
- `strictProper_biproduct`.
- `compactSupportStrictScalarMate`.

The final compactSupportStrictScalarMate is still unproved. Its finite-evaluation
normalization and proper biproduct identities are not supplied by the categorical
proofs in this packet. Existing remaining obligations retain their original
source and complete natural-language proof docstrings.

## No longer needed

Removed the following unused immediate proof imports:

- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
- `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`.
- `Sheaf.Paper.FiniteFreeScalarExtension`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`.
- `Sheaf.Paper.CompactSupportReductionTower`.
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`.

These imported modules supply no declaration used directly by the proofs completed
here. Some remain transitive statement dependencies, and their nodes also remain
part of the plan for the eleven outstanding original obligations; this partial packet
does not claim they can be withdrawn globally. No module is deleted, no source-library
declaration is removed, and no node is globally pruned. Public statement imports stay
unchanged. Added only the private proof import
Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionResolution; retained the
RightDerivedFunctor.Comp import for reindexProper.

The direct use of lem-sp-strict-tower-arithmetic-restriction-resolution is as an
existing proved general arithmetic-restriction tool, preserving the unit's
coefficient-compatibility route. No tool_uses approval was added by the worker.

## Where the brief, the DAG or earlier work was wrong

The ordinary base-site open tensor invertibility did not need a new sectionwise balancing
proof: its two mate operations are conjugation of the already invertible actual
pullback/restriction square. The geometric-transpose formulas and proper/open
pasting likewise reduce to the existing categorical mate calculus. No statement
was found false and no repair or consumer adaptation was needed.

Validation: lcompile.py compiled the full item module successfully (59.8 seconds),
followed by the delivery
compile and preflight. The unit record sk-thm-sf-compatibility is unchanged; none
of its realized statement or proof steps is bypassed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
