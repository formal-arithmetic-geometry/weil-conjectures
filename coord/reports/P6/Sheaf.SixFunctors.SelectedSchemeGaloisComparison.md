## What changed

Proved `WeilConjectures.TraceFormulaCoefficientConventions.comparisonCoefficientAnnihilator`
in `Sheaf.SixFunctors.SelectedSchemeGaloisComparison`, with the explicit witness
`T.coefficients.l ^ T.level`. The spectral norm puts the coefficient prime in the
recorded maximal ideal; `Ideal.pow_mem_pow` puts its level-th power in the defining
quotient ideal. The quotient map kills that power, so it annihilates all elements.
The finite-field cardinality determines characteristic p, and the distinct prime l
is nonzero, hence invertible, in the geometric base field.

Added the private proof import `Mathlib.Algebra.CharP.CharAndCard`. Both public
imports, all declaration signatures, and both comparison selections are unchanged.
The existing eight-step scheme/Galois route is retained through the publicly
imported `Sheaf.SixFunctors.SchemeGaloisComparison`; the node now additionally records
this finite-coefficient specialization. No definition or statement repair was needed.

Validation: the final file compiled cleanly through lcompile.py (8.8 seconds).
The argument handles ramified extensions, level one, l = 2 with p different from 2,
and arbitrary positive levels. No geometric nonemptiness assumption is used.
The same ideal-power calculation even holds at level zero (the zero quotient),
although the existing conventions require a positive level.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.TraceFormulaCoefficientConventions.comparisonCoefficientAnnihilator`
(node `prop-trf-scheme-galois-comparison`). No sorry remains in the item.
Added 0 holes, split off 0 statements, and introduced no new declarations.
This is a proof from the existing DVR interface, not a decomposition. The
underlying scheme/Galois comparison theorem remains an imported dependency;
this delivery does not claim to prove that separate theorem.

## No longer needed

Removed these direct private imports, none of which the proof or definitions use
beyond the two retained public imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`
- `Sheaf.AlgebraicGeometry.FrobeniusFactorization`
- `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism`
- `Sheaf.SixFunctors.SchemeFrobenius`
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`

These modules remain dependencies of the generic comparison or coefficient
conventions through the retained public imports. Thus no DAG dependency or globally
reachable module is claimed pruned. In particular, the eight-step comparison route
and its unit obligations remain intact; the finite-level wrapper need not import
its implementation dependencies a second time.

## Where the brief, the DAG or earlier work was wrong

The module had inherited proof imports for the generic comparison, although its
only hole is the coefficient annihilator. Its node recorded the generic eight-step
comparison construction but omitted this finite-level arithmetic verification;
the appended step supplies it without replacing the generic route. The existing
docstring's unspecified power can be chosen concretely as l^level because
l lies in the maximal ideal. No mathematical statement was changed. No tool
failure, forced adaptation, or new node.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
