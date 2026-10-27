## What changed

Proved `WeilConjectures.residue_controlled_finite_homs` in
`Sheaf.Paper.ResidueControlledFiniteHoms`, preserving its exact signature and
`integralFiniteInternalHom` unchanged. The proof derives invertibility of the coefficient
prime in every residue field from the finite-field datum, applies `integral_residue_tor`
to both inputs, extracts finite-level constructibility, and applies the existing
`finite_constructible_derivedHom_proEtale` with the supplied residue intervals.

A fully proved private helper `support_of_torAmplitude` tests any intrinsic pro-etale
Tor-amplitude assertion against the coefficient unit in degree zero. Essential
surjectivity supplies a representative, `exists_isKFlatResolutionGeneral` supplies a
K-flat resolution, and the localized ordinary complex right unitor identifies that
Tor test with the original object. No boundedness or perfectness hypothesis is added.
The helper applies to arbitrary commutative coefficients, including the zero ring.

Added private proof imports of `Sheaf.Algebra.Homology.KFlatResolutionGeneral`,
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`,
`Mathlib.Algebra.Homology.Monoidal`, and `Mathlib.Algebra.CharP.CharAndCard`.
Updated only the permitted proof fields of the existing node to record the resolution
and tensor-additivity tools used in the final step. No definition, public signature,
public import, upstream declaration, or consumer changes.

Validation: the complete module compiled without warnings through `lcompile.py`
(exit code 0, 9.6 seconds). The argument uses the same formula also for n = 0
(exponent one), d = 0, zero inputs, and the empty scheme; none requires a separate
nonemptiness or positive-dimension hypothesis.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.residue_controlled_finite_homs`
(node `lem-coef-residue-controlled-finite-homs`). The private helper is fully proved.
Zero holes remain in the delivered module; zero holes added; zero statements split off.
The existing imported `finite_constructible_derivedHom_proEtale` remains an external
stated dependency, as intended by the stage-3 brief. This delivery proves the assigned
statement from the recorded dependencies; it does not claim that their full axiom
closure is already sorry-free.

## No longer needed

Removed unused private imports `Sheaf.Paper.FiniteTorAmplitudeSites` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.
The former supplies the etale presentation, while this proof uses the intrinsic
pro-etale predicate already available through `FiniteConstructibleHom`. The latter
supplies tensor on fixed-ring module sheaves; the Tor predicate here uses the intrinsic
representative-level `AlgebraicGeometry.Scheme.derivedTensor`, already in scope.
Neither module is claimed globally unnecessary: both retain other consumers.
All six original declared mathematical proof dependencies remain needed, with the
intrinsic implementation of the derived-tensor step. No nodes or modules withdrawn.
The unit route is unchanged, and no integral Hom reconstruction is needed here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the stated plan. Its final tensor-unit step needed explicit
K-flat resolution existence and tensor additivity in Lean. The node now records the
existing `lem-pc-kflat-resolution` and
`lem-weil-pbc-independent-bounded-flat-kflat` tools for these points. The current primary
attachment of `def-weil-derived-tensor` names the fixed-ring presentation; this proof
uses the retained intrinsic presentation matching `HasProEtaleTorAmplitude` directly,
without asserting an identification of the two categories or changing their definitions.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
