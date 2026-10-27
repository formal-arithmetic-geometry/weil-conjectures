## What changed

Constructed the symmetric graded extension explicitly, using the normalized tensor-pullback
adjunction and the symmetric algebra universal property into the direct sum of tensor-power
sections. Proved extension uniqueness by induction on the symmetric degree. Proved coefficient
normalization, the degree-one quotient coefficient formula, frame change, source restriction,
and affine base restriction.

The generator cover is proved from affine surjectivity of the quasi-coherent quotient and the
bijective tensor-pullback sections comparison: tensor induction puts the coefficient of a frame
in the ideal of generator coefficients, so that ideal contains 1. A stalk basis calculation
then proves generation everywhere. The overlap unit calculation uses ordinary localization.
Chart equations and cancellation of the affine Proj open immersions prove frame independence;
homogeneous-fraction surjectivity and equality on the generator cover prove uniqueness of the
scheme morphism.

The geometric construction for the affine-basis graded-line-map interface is isolated in
Sheaf.TraceFormula.GradedLineHomogeneousFractionAtlas. It has its own source and node, and
assumes a graded map and generation everywhere. It neither constructs a symmetric extension
nor proves quotient surjectivity, coefficient compatibility, frame independence or uniqueness
of the quotient morphism. The assigned theorem combines this result with those proved steps.
Private helpers also prove that the supplied recursive frame powers are bases and that
the normalized general coefficients define a ring homomorphism on the whole graded algebra.
The homogeneous-fraction homomorphism is obtained by the ordinary localization map, composed
with the inclusion of the degree-zero homogeneous localization; its fraction formula is proved.
The remaining atlas construction requires geometric gluing and the canonical-map characterization.
All old public declarations and definition bodies are preserved; all helper constructions and
proofs in the assigned module are private. Added imports are proof imports.

To control elaboration, the symmetric lift, component maps and graded restriction map are
private irreducible constructions with proved evaluation lemmas. Tensor associativity and
commutativity use explicit section arguments, and inverse-unitor naturality is applied directly.
The development profile and temporary elaboration stop have been removed from the module.

## Proved and sorry left

The original module has one hole, in
AlgebraicGeometry.Scheme.Modules.line_quotient_homogeneous_fraction_map.
Its proof is replaced by the construction and combination described above.
One separate hole is added in
AlgebraicGeometry.Scheme.Modules.graded_line_homogeneous_fraction_atlas
(node lem-trf-graded-line-homogeneous-fraction-atlas).
This is a decomposition: one original hole closed, one new hole added, net zero.
No definition or private declaration contains sorry.

## No longer needed

Removed the unused proof import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal.
The relative Proj chart embeddings and their open immersion instances are already supplied
by RelativeProj.Basic through the unchanged public interface.

The proof does not use lem-trf-line-proj-affine-chart-atlas
(Sheaf.TraceFormula.LineProjAffineChartAtlas): its statement requires homogeneous module
sheaves and a sheaf-level decomposition, whereas the supplied RelativeGradedLineMap and
canonical symmetric algebra are affine-basis data. The new general atlas states the needed
construction for that interface; it does not duplicate the sheaf-level statement.
The proof also does not apply lem-trf-space-line-module-proj-map or
its def-trf-space-line-module-proj-input: their test-family interface would require a separate
cartesian presentation and coherence construction. The canonical scheme characterization is
provided directly by the general affine-basis atlas. Those modules remain public imports of
GradedImmersionAmpleCriterion; no claim is made that they leave the target closure.

The named symmetric-grading result lem-weil-pbc-symmetric-algebra-graded is not applied by
this proof: the unchanged canonical graded algebra already supplies its concrete grading.
The proof uses induction on the generator-range powers and Mathlib's symmetric-algebra lift.
No longer-needed declarations or modules are deleted.

## Where the brief, the DAG or earlier work was wrong

The plan's instruction to apply the existing line-Proj affine chart atlas directly does not
match the Lean signatures. That atlas takes RelativeProjAlgebra with actual homogeneous
sheaves and their tensor-pullback maps. The assigned statement takes GradedAlgebraData and
RelativeGradedLineMap on affine base opens. No bridge between these presentations is supplied.
The new node records the missing geometric construction using the actual input interface.

The affine section argument proves the generator ideal is already the unit ideal on each
whole affine W. This avoids the plan's separate local representation of each lifted stalk.
Empty source opens and zero rings satisfy the same ideal and localization equations;
nilpotent or zero coefficients merely give empty localization charts.

The first delivery attempt (`delivery-first.log`) was refused by the split-off policy at
64/120 reference minutes. The resumed sandbox records reference start
2026-10-23 16:48:14 UTC. The earlier work and compile logs were retained across the launcher
pause; no budget metadata was changed. Work continued on the atlas coefficient algebra.

## New nodes

lem-trf-graded-line-homogeneous-fraction-atlas, in
lean/Sheaf/TraceFormula/GradedLineHomogeneousFractionAtlas.lean, isolates the general
homogeneous-fraction construction of Stacks Tags 01NK and 01O9 for affine-basis graded line
maps. It is a strict part of the assigned argument: it assumes the already constructed map
and its generation, and supplies the geometric map and local fractions. Its theorem has
exactly one sorry and a complete proof in words. No change record for a public interface is
needed because existing public statements, definitions and public imports are unchanged.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
