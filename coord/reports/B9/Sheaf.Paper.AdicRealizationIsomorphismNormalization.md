## What changed

Replaced the original hole by a complete Lean assembly of the prescribed realization
reindexing argument. A proved private constructor transports the supplied realization's
exactness, full faithfulness and essential image through its section-module equivalence;
its realization, tensor and finite-normalization fields retain the supplied data exactly.
The assembly obtains a normalized FamilyCore, proves the Family fields from separate
functoriality, tensor/unit and evaluation-transpose obligations, and proves the final
common-stage scalar equation directly by naturality on StageSystem.isoToStage.

Four new public theorem modules state the remaining genuine subarguments. They contain
no definitions, choices of arbitrary objects, new hypotheses on the assigned theorem,
or changes to existing signatures. The assigned theorem and original docstring remain
unchanged. The DAG now follows the actual assembly; the original eight-step route is
retained below its new intermediate nodes.

## Proved and sorry left

Closed the textual hole of
WeilConjectures.AdicQbarRealization.adic_realization_isomorphism_normalization
(lem-sf-adic-realization-isomorphism-normalization). Its objectwise constructor and
assembly proof are complete, and its final scalar equation is naturality.

This is a decomposition, not a claim that the original theorem is sorry-free in its
axiom closure: zero of the original one mathematical obligations is completely closed.
Four holes are added, each the whole proof of a public theorem in its own module:

- WeilConjectures.AdicQbarRealization.exists_normalized_reindexing_core
  (lem-sf-adic-reindexing-core): construct only FamilyCore, integral normalization and
  section/source-unit normalizations, without the comparison coherence laws.
- WeilConjectures.AdicQbarRealization.normalized_reindexing_functoriality
  (lem-sf-adic-reindexing-functoriality): derive identity/composition from normalized
  comparison data, without constructing those data or tensor/Hom laws.
- WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor
  (lem-sf-adic-reindexing-tensor): derive tensor/unit compatibility from the integral
  normalization and the fixed finite quotient tensor normalizations.
- WeilConjectures.AdicQbarRealization.normalized_reindexing_hom
  (lem-sf-adic-reindexing-hom): derive the permitted Hom equation from tensor compatibility
  by evaluation/transposition, without assuming or constructing integral normalization.

Validation: lcompile.py --all compiled the four new theorem modules; a subsequent
single-file compile of the completed assembly passed in 11.8 seconds. The delivery
command runs its own declaration/axiom probe and server preflight.

All remaining statements retain arbitrary underlying scheme isomorphisms. Edge cases
checked in their mathematical formulations: empty schemes, zero inputs, identity
isomorphisms, trivial coefficient extensions and inputs with different finite stages.
The source-identity unit assumption fixes the identity against the actual compositor;
no inference from equality of finite reductions is used. The new nodes and docstrings
include the whole-cone and raw common-stage descent argument.

## No longer needed

No mathematical dependency or module is pruned: the former proof dependencies remain
needed by the intermediate nodes. Removed these direct proof imports from the item,
because the assembly uses the new intermediate statements instead:

- Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.PurInverseImageTensorHom
- Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
- Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
- Sheaf.Paper.IsomorphismComparisonNatural
- Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
- Sheaf.Paper.IsomorphismDerivedPullback
- Sheaf.Paper.FiniteFreeCompletedScalarComparison
- Sheaf.Paper.IsomorphismComparisonScalarExtension
- Sheaf.SixFunctors.ConstructibleTensorCompletion
- Sheaf.Paper.DerivedPullbackTensorIso
- Sheaf.Paper.DerivedAutomorphismHomEvaluation
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
- Sheaf.Paper.IntegralInverseImageComparisonComposition

Obsolete direct tool-use approvals on the parent are removed for the following nodes:
lem-weil-proetale-isomorphism-inverse-image, sk-prop-sfb-cartesian-coefficients,
sk-prop-sfb-qlbar-colimit-x, lem-pur-isomorphism-inverse-image-tensor-hom,
lem-sfb-exact-monoidal-equivalence-total-kflat,
lem-weil-isomorphism-derived-pullback-comparison-normalization,
lem-weil-isomorphism-comparison-natural, lem-pur-cochain-pullback-tensor-coherence,
lem-weil-isomorphism-derived-pullback,
lem-weil-finite-free-completed-scalar-comparison,
lem-weil-isomorphism-comparison-scalar-extension, lem-fix-constructible-tensor-completion,
lem-pod-derived-automorphism-hom-evaluation, lem-pur-derived-pullback-tensor-iso,
and lem-trf-integral-inverse-image-comparison-composition. The underlying lemmas
remain dependencies of the subarguments, and are not asserted to be globally unused.
All existing public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

The existing declarations give the coefficient/integral/tensor ingredients, but do not
state their assembly into the native FamilyCore and its comparison laws. The new
statements make these missing bridges explicit. The final displayed common-stage
square is already naturality; the nontrivial scalar normalization belongs in
integralRealizationAgreement and the comparison descent, rather than this last equation.
No existing statement is disputed or weakened. No unit route changes.

## New nodes

lem-sf-adic-reindexing-core: the construction/descent part of original steps 1--5,
including normalized ambient tensor reindexing and the source identity, before the
comparison's coherence equations.

lem-sf-adic-reindexing-functoriality: original step 8 for fixed normalized comparison
data. The ordinary section equations and source-unit equation are retained as hypotheses.

lem-sf-adic-reindexing-tensor: original step 6, retaining the actual completion cocone,
K-flat representative equations and coefficient-unit normalization.

lem-sf-adic-reindexing-hom: original step 7, a strictly partial evaluation-transpose
argument assuming tensor compatibility and preserving the permitted-pair domain.

These are new theorem statements only. No existing definition or public interface
changes, no consumer adaptations, and no change record is required.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
