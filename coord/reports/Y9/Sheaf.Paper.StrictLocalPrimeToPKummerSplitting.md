## What changed

Proved `AlgebraicGeometry.strictLocalPrimeToPKummerSplitting` in
`Sheaf.Paper.StrictLocalPrimeToPKummerSplitting` from the six existing extracted
subarguments and the regular-local/normality and strict-henselian section APIs.
All existing public statements, definitions and public imports are unchanged.
Private proved helpers handle parameter permutation, localization scalar towers,
base-change comparisons and the section of the finite étale model. The normalization
assembly is proved for an abstract regular root ring, then instantiated at the displayed
quotient; this avoids expensive unfolding of its multivariate-polynomial presentation.
The DAG still follows the simultaneous-root/DVR/regular-extension route. Its first and
last steps now record the actual choice n = 1 when r = 0 and n = |G| otherwise.

## Proved and sorry left

Closed 1 existing hole: `AlgebraicGeometry.strictLocalPrimeToPKummerSplitting`
(node `lem-sfb-strict-local-prime-to-p-kummer-splitting`). Added 0 holes; split off 0
statements. No `sorry` remains in the item module. The six previously stated inputs
are imported as requested by stage 3; their existing unfinished proofs are unchanged.

## No longer needed

Removed direct private imports of:

- `WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`
- `WeilConjectures.RingTheory.RegularPrincipalPrimeLocalizationDvr`
- `WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenGenericAlgebra`
- `WeilConjectures.RingTheory.EtaleNormalRing`
- `WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`
- `WeilConjectures.RingTheory.DvrGaloisNormalizationRamificationDvd`
- `WeilConjectures.RingTheory.DvrTameTensorFactorUnramified`
- `Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion`
- `WeilConjectures.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension`

These low-level inputs belong to the retained extracted subarguments rather than the
assembly proof. They are still needed there: no node or library module is withdrawn,
and no approved tool-use entry is removed. All ten existing DAG proof dependencies
remain used. There are no pruned modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The earlier 20-step docstring
expands the already extracted subarguments; the current DAG correctly groups those
steps into six existing inputs. The n = 1 empty-boundary condition is most directly
handled by choosing that exponent at the start, since no boundary-prime degree
condition then needs to be checked. No source-library declaration was changed.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
