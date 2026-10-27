## What changed

Proved WeilConjectures.PurScalarProjection.ordinaryCompletedSquare in
Sheaf.Paper.CompactSupportScalarProjectionIdentification. The proof uses the existing
compactSupportProjectionCoefficientChange ordinary square. After precomposition by
scalar extension of the E source completion unit, integralMap's defining inverse unit
cancels. Naturality of the support comparison and completion units, together with the
scalarCompletion and scalarTensorCompleted unit equations, gives that ordinary square
postcomposed by compact support of the F inner unit. integralDomains makes the source
unit invertible, so cancellation proves the required completed square.

The scalar constructibility domains come from compactSupportCoefficientModels_scalar.
The positive ramification exponent is obtained from the already proved private
integral_ramification helper; its uniformizer equation gives the ideal equation.
Added proof-only imports of CompactSupportProjectionCoefficientChange,
CompactSupportCoefficientModels, and all CompletedIntegralFiniteFree.
Local irreducibility attributes keep the coefficient inclusion and canonical scalar/tensor,
scalar/pullback and support comparison maps abstract during elaboration. No definition
body changes. All existing Lean signatures, definitions, visibility and public imports
are preserved.
The proof applies also to identity extensions, zero inputs and the empty scheme;
it never infers integral equality from equality of reductions.

Updated the item's node proof and dependencies. Corrected the ordinary-square node's
broad parent-theorem dependency to the existing coefficient-data interface, as detailed
in coord/changes/ordinary-projection-coefficient-dependencies.md. This is a node-only
clarification: the generic theorem's Lean signature and mathematical content do not change.
No new module, theorem hole or node is introduced. This is a partial delivery for a
module with multiple original holes.

Validation: lcompile.py compiled the complete final item cleanly in 53.6 seconds.
Temporary profiler options were removed. A read-only dependency audit found no path
back to the item from any dependency added by this route. The statement-change
record validates, and both changed nodes have proof_deps equal to their proof-step uses.

## Proved and sorry left

Closed 1 of the 7 original local holes:
WeilConjectures.PurScalarProjection.ordinaryCompletedSquare.
Added 0 holes and split off 0 statements.

The six local sorries left, all attached to
lem-pur-compact-support-scalar-projection-identification, are:

- WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique
- WeilConjectures.PurScalarProjection.properProjection_existsUnique
- WeilConjectures.PurScalarProjection.openProjection_existsUnique
- WeilConjectures.PurScalarProjection.realization_existsUnique
- WeilConjectures.PurScalarProjection.native_scalar_identification
- WeilConjectures.PurScalarProjection.gamma_identification

The imported ordinary compactSupportProjectionCoefficientChange is an existing named
sorry of lem-pur-compact-support-projection-coefficient-change; it is not a new hole.
The proof also uses the existing local scalarCompletion_existsUnique through its
unit-normalized isomorphism. Thus no claim of an axiom-free entire module is made.

## No longer needed

No Lean imports or modules are removed or withdrawn.
For ordinaryCompletedSquare the invertible constructible source unit suffices: the
arbitrary complete-target reflector Hom bijection and a new direct calculation of
proper/open scalar compatibility are unnecessary. Those general comparisons remain
needed by the other six local obligations, so their existing dependencies are retained.

The generic ordinary-square node no longer depends on
lem-pur-compact-support-integral-coefficient-comparison: it uses only the coefficient
data and formal mate-pasting identity, not that parent's completed projection theorem.
Its statement interface now cites def-pur-integral-compact-support-coefficient-data.
No declaration is removed from the adopted source library or any other module.

## Where the brief, the DAG or earlier work was wrong

The original plan used a general reflector uniqueness argument for the constructible
square. The actual integralMap source unit is already invertible by integralDomains,
which makes cancellation a shorter route.

The generic ordinary-square node had unnecessarily cited the whole parent integral
coefficient-comparison theorem. That parent depends on this item's completed square.
Only defining coefficient maps and their proved formal factorization are used, so
retaining the parent edge would give an artificial cycle. The dependency-interface
correction preserves the theorem and all its consumers.

## Statement corrected

Only the explanatory dependency reference of
lem-pur-compact-support-projection-coefficient-change changes. Its Lean signature,
hypotheses and conclusion are byte-for-byte unchanged. The old reference to
lem-pur-compact-support-integral-coefficient-comparison is replaced by the existing
coefficient-data interface; the ordinary argument follows Stacks 07A6, 0E48 and 0E8I.

Its only existing DAG citer, lem-sf-concrete-integral-projection-cone, holds unchanged:
it applies exactly the same ordinary coefficient square. No Lean consumer needs adaptation.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
