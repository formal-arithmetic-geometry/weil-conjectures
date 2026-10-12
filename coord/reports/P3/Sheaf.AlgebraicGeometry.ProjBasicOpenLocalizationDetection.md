## What changed

Proved `AlgebraicGeometry.Proj.basicOpen_localization_detection` with its original signature
and visibility. Added four fully proved private helpers in the same module: the grading
polynomial ring homomorphism, its coefficient formula, homogeneity of the prime-localization
kernel, and detection for homogeneous numerators. Added proof-only imports
`Mathlib.Algebra.Polynomial.AlgebraMap`, `Mathlib.RingTheory.Ideal.Colon`, and
`Mathlib.RingTheory.GradedAlgebra.Radical`. Updated the existing node's proof and proof_origin. The second reader replaced the unused
public twisting-sheaf import with `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`,
which supplies the Proj basic-open types used in the unchanged statement.

The proof applies McCoy directly to grading polynomials over A_p, then uses homogeneous
annihilators, prime existence, homogeneous cores, and the finite homogeneous decomposition.
It introduces no auxiliary graded localization and no postponed statements.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Proj.basicOpen_localization_detection`
(node `lem-sc-proj-basic-open-localization-detection`). All four new private helpers are proved.
Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.

The single-file compile is clean. The argument covers the zero ring, nilpotent f (including
f=0), zero numerators, and arbitrary finite sets of homogeneous components. If f is nilpotent,
the assumption that a homogeneous numerator survives in A_f already contradicts the
annihilator's disjointness from powers of f; no prime or nontrivial-ring assumption is added.

## No longer needed

Removed the unused import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`, replacing it with
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`. No DAG proof-dependency node is
removed: the original `proof_deps` is empty. Every added proof import is used. This module
no longer needs the twisting-sheaf module; it remains reachable elsewhere, so no whole-library
module-pruning claim is made. The planned auxiliary localization at homogeneous denominators,
its Z-grading, its injection into A_p, Laurent polynomials, and a common exponent killing
all components are unnecessary. None had a separate node/module in the original plan.
No Sheaf statement with an unproved dependency is imported.

## Where the brief, the DAG or earlier work was wrong

The node's proof was one unsplit paragraph with no dependency declarations. It can be
proved directly from Mathlib. Its auxiliary-localization argument is correct but unnecessary:
map grading polynomials straight to A_p[X], where a denominator outside p has a unit
coefficient. McCoy then proves the kernel is homogeneous. The source Tag 01M7 states
standard-open sections and stalks; equality detection for all ordinary fractions is the
additional algebraic argument supplied by the existing node, now fully formalized.
The unit's route and every existing statement remain unchanged. No new nodes or forced
adaptations are needed.

## Second reading by P3

1. PASS: Compared the complete Lean diff with the repository version. The existing theorem's
signature is byte-for-byte identical, including hypotheses, conclusion and visibility; its
existing docstring is unchanged. No existing definition changed, and there are no adaptations
or statement/definition change records. The import change is documented separately.
The only new declarations are four private, fully constructed/proved helpers.
2. PASS: Independently compiled the delivered file without errors or warnings. In a scratch
copy, `#print axioms` for `gradingPolynomial`, `gradingPolynomial_coeff`,
`localization_kernel_isHomogeneous`, `homogeneous_localization_zero`, and
`basicOpen_localization_detection` showed exactly `propext`, `Classical.choice`, `Quot.sound`.
There is no sorry, custom axiom, unsafe/opaque declaration, external implementation, or
unproved witness choice. The grading polynomial is an explicit direct-sum construction.
3. PASS: No statements are split off and no holes are added. Read all private helpers: the
McCoy step uses a unit coefficient, not an assumption that all denominators are homogeneous;
the homogeneous annihilator argument uses injectivity of addition of natural degrees.
The zero ring, zero numerator, nilpotent or zero f, and empty basic open introduce no hidden
nontriviality assumption. Independently searched LeanFinder for homogeneity of localization
kernels, Loogle for coefficient/nonzero-divisor results, and rg over Mathlib and the project
for localization kernels, grading polynomials and homogeneous annihilators. Found McCoy's
existing criterion already used by the proof; no exact helper or shorter detection theorem.
4. PASS after import repair: The proof reduces equality to numerator vanishing, then to its
homogeneous components, and uses proved Mathlib facts throughout. There are no postponed
Sheaf lemmas and no old proof dependencies to prune. Read
`dag/units/sk-thm-picard-duality.json`; its statement, step and realized record are unchanged,
and this local algebraic proof bypasses no unit. Replaced the unused public twist-module
import by the basic Proj module. The sole direct consumer, `ProjTwistBasicOpenFractions`,
imports the twist module publicly itself, so this removal requires no adaptation.
5. PASS: Compared the node JSON diff. Only `proof` and `proof_origin` change; the four steps
match the grading polynomial, homogeneous kernel, annihilator/prime argument, and finite
component sum actually used in Lean. `proof_deps` stays empty, correctly recording that no
DAG lemma is invoked. The statement, Lean statement record, unit and chapter are unchanged.
No new node is needed for a postponed statement because there is none.

Import change record: `coord/changes/ProjBasicOpenLocalizationDetection-imports.md`.

Second reading changed only the unused import, its required change record and the report; the proof was
already correct. Holes closed: `AlgebraicGeometry.Proj.basicOpen_localization_detection` (1).
Holes added: none (0). The revised import set also compiles cleanly.
