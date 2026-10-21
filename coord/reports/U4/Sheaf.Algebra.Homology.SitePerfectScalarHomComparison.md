## What changed

Replaced the hole in `CategoryTheory.sitePerfectScalarHomComparison` by a proof from
canonical scalar tensor monoidality and perfect duality in the same fixed coefficient
presentation. The comparison remains the original specified transpose. Private lemmas
prove its evaluation identity and naturality in both variables without perfectness,
identify the tensor-dual evaluation with `ihomUnitTensorToIhom`, and apply the existing
proved strong-monoidal Hom comparison theorem.

Added `Sheaf.CategoryTheory.RingedSitePerfectDualityForModel`, proved using the existing
perfect-duality proof's slice-restriction and strict-perfect evaluation lemmas. It
quantifies over the specified normalized presentation, as this item requires. Its proof
import uses `import all` to reuse those private proved lemmas.

Added `Sheaf.Algebra.Homology.RingedScalarTensorMonoidal`. Its statement concerns only
strong monoidality of scalar extension with a supplied canonical normalized tensor
comparison. The comparison and both normalization formulas themselves come from the
existing `ringedFiniteFreeHomBaseChange_tensor` theorem. This separate scalar-monoidality
result contains the one remaining hole.

All existing public signatures, definitions and public imports are preserved. New proof
imports are private. The source library is unchanged. The change record
`coord/changes/U4-site-perfect-scalar-hom-proof-environment.md` records the added open
command and local elaboration attributes requested by the static command scan.

## Proved and sorry left

Closed the original hole in `CategoryTheory.sitePerfectScalarHomComparison`.
Proved the new theorem `CategoryTheory.ringedSitePerfectDualityForModel`
(node `lem-fix-ringed-site-perfect-duality-for-model`) without additional holes.

Added one hole: `CategoryTheory.ringedScalarTensorMonoidal`
(node `lem-fix-ringed-scalar-tensor-monoidal`). No hole remains in the item module.
This is a decomposition, with one original hole closed and one strictly lower hole
added, not a claim of net hole reduction. The remaining statement has no perfect
object, internal-Hom comparison, comparison naturality or evaluation conclusion.
Its data are fixed by the supplied generator and K-flat normalization equations;
its monoidal unit is determined by the tensorator and the unit laws.

## No longer needed

Removed the direct proof import of `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
Its node `lem-sfb-ringed-derived-monoidal-comparisons` is no longer a direct dependency
or tool use of this item. The replacement scalar monoidality statement retains the
independent universes this item actually uses. No existing module or declaration is
withdrawn.

The separate node `lem-fix-closed-evaluation-dual-criterion` and its module
`Sheaf.CategoryTheory.ClosedEvaluationDualCriterion` are not needed by this proof:
the existing proved `MonoidalClosed.exactPairingOfIsIso` constructs the required exact
pairing from the component at P alone. The two-variable naturality and evaluation
calculations also require no perfectness hypothesis.

The original direct import of `Sheaf.CategoryTheory.RingedSitePerfectDuality` is replaced
by the specified-presentation lemma; that module remains a private proof dependency of
the new lemma. Its biduality and perfectness-of-the-dual conclusions are unused here.
No claim is made that these existing modules are globally unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The planned monoidal-comparisons interface packages a site with equal object, morphism
and coefficient universes. This item's pro-etale site has different object and morphism
universes, and its coefficient and derived universes remain independent. That interface
cannot be specialized literally to the declared statement. The scalar-monoidality
lemma states the required independent-universe result, preserving the source argument.

The existing perfect-duality theorem returns a presentation after P is chosen. The
item needs one scalar/tensor presentation for every perfect P. Reusing its proof for
an arbitrary specified `RingedSiteDualityModel` resolves the quantifier mismatch without
changing any existing statement.

The generic evaluation criterion was more than this proof needs. The existing
`exactPairingOfIsIso` and strong-monoidal Hom comparison suffice after the explicit
symmetry/unit calculation. Zero objects, the zero coefficient ring, identity scalar
maps, non-flat scalar maps and unbounded Q do not introduce additional hypotheses.

## New nodes

`lem-fix-ringed-site-perfect-duality-for-model` records the proved fixed-presentation
form of the all-target evaluation isomorphism of Stacks 08JJ. Its module reuses the
existing local finite-projective argument and has no new hole.

`lem-fix-ringed-scalar-tensor-monoidal` records strong monoidality for a canonical
normalized derived scalar tensor comparison with independent universes. Its source is
Stacks 07A4 with the derived constraints of 0FPT. Its full proof in words specifies the
unit construction and descent of the associativity and action-unit diagrams. This is
the remaining separate result. No existing definition or statement was changed.
`coord/changes/U4-site-perfect-scalar-hom-proof-environment.md` records only the local
proof environment; no consumer adaptation is required.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
