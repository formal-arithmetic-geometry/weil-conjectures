## What changed

In Sheaf.SixFunctors.FrobeniusCohomologyTransportIso, proved
WeilConjectures.frobeniusCoefficientModulesTower_existsUnique by an explicit
linear equivalence assembled from Mathlib's lifted tensor equivalence and
base-change cancellation. Three proved private helpers give the equivalence,
its prescribed pure-tensor formula, and naturality. Double tensor induction
proves uniqueness. No signatures or existing definition bodies changed.

Proved WeilConjectures.frobeniusCohomologyStageEmbedding_comp by ring-hom
extensionality and cancellation of the larger stage's Shrink algebra equivalence.
The edge case E = L is included without a strict-inclusion hypothesis.
Preserved its full signature and suppressed the unused-section-variable linter
locally because the proof does not need algebraic closedness.

Added a private proof import of Mathlib.LinearAlgebra.TensorProduct.Tower.
The node proof records these two completed coefficient-realization steps; its
remaining transport argument and declared proof dependencies are retained.
This is a partial delivery of two of the module's six original proof holes.

## Proved and sorry left

Closed 2 original holes, added 0:

- WeilConjectures.frobeniusCoefficientModulesTower_existsUnique.
- WeilConjectures.frobeniusCohomologyStageEmbedding_comp.

Four original holes remain unchanged, all attached to
lem-weil-frobenius-cohomology-transport-iso with their existing source and proof
docstrings:

- WeilConjectures.frobeniusCohomologyRationalOperationScalar_existsUnique.
- WeilConjectures.frobeniusCohomologyQbarFunctor_existsUnique.
- WeilConjectures.frobeniusCohomologyTransport_isIso.
- WeilConjectures.frobeniusCohomologyTransport_natural.

No holes were split off. The private helpers are completely proved.
Validation: the full module compiled through lcompile.py after the two proofs;
the pruned import list compiled successfully. A delivery compile then hit the
60-second limit; profiling identified repeated elaboration of the private tensor
construction. Making that helper locally irreducible after its formula theorem
reduced the next whole-file compile to 41.4 seconds. Delivery preflight
also checks declaration axioms and direct sorry use.

## No longer needed

Removed these direct proof imports, which the retained public imports already
supply where the unchanged statements and definitions need their contents:

- Sheaf.SixFunctors.FrobeniusPointTransportNatural
- Sheaf.SixFunctors.FrobeniusSquareCartesian
- Mathlib.AlgebraicGeometry.Sites.Proetale
- Sheaf.SixFunctors.FrobeniusPointTransport
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
- Sheaf.Paper.SfRationalizationKaroubi
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
- Sheaf.Paper.FrobeniusGeometricExchange
- Sheaf.Paper.CondensedAmbientExchange
- Sheaf.AlgebraicGeometry.ChosenCartesianSquare
- Sheaf.CategoryTheory.MateIsoAlongEquivalences
- Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence
- WeilConjectures.Compactification.Refinement
- WeilConjectures.Compactification.CategoryBaseChange
- Sheaf.Paper.CompactificationCoherence
- Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
- Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
- Sheaf.Paper.SfIntegralConstructible
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
- Sheaf.Paper.IntegralDerivedOperationsOnSlices

No declaration or module is withdrawn. No whole DAG dependency is claimed
unnecessary: the remaining transport holes still need their recorded argument,
and the retained public interface reaches many of the removed direct imports
transitively. All existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The module has six original holes, rather than only the two concluding transport
theorems. Its four coefficient-realization support theorems are substantive
obligations too. The existing DAG's three-step assembly does not separately
name these implementation-level normalization obligations; the node proof now
records the two completed ones. The old nine-step transport docstring is older
than the node's extracted three-step plan; it was left unchanged.

The generic finite/system exchange inverse statements use fiberMap into the
geometric fiber of the finite-field point; this module deliberately uses the
actual Spec k and its structure map. They therefore require coordinate
comparison when completing the remaining transport theorem. This partial
delivery does not replace that theorem by a renamed obligation or weaken it.

Proof-context change record: coord/changes/Z6-frobenius-coefficient-tower-proof-context.md.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
