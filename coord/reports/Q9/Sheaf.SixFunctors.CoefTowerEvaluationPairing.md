## What changed

Extracted the existing construction block into
`Sheaf.SixFunctors.CoefTowerEvaluationPairingData`, publicly reexported from the
original module. All existing construction signatures, bodies, instance proofs,
visibility and public imports are preserved. The extraction permits the two
independent comparison lemmas to import the definitions without importing the
assembly theorem. It is not a compile-time workaround.

The assembly preserves the exact statement of
`WeilConjectures.coefTowerEvaluationPairing`. It takes the compactification and
finite pairing witnesses from `coefPairingCompactificationModels`, applies
`coefPairingHomRepresentativeComparison` to the same calculus, transports the
integral finite Hom comparisons along eQ, and factors the two Hom descriptions
by isomorphism cancellation. The final identity uses a direct proof of
`coefPairingSystem_dinaturality` on arbitrary system objects, applied to the
reduction of f. Finite evaluations are never used to detect equality of maps.

Change record: `coord/changes/Q9-pairing-data-extraction.md`. Its user table lists
all 76 downstream modules; each retains the identical reexported API and needs
no adaptation. A parsed declaration comparison checks all 31 original signatures
unchanged; a byte comparison checks the relocated construction block unchanged.

Validation: `lcompile.py --all` compiled all five delivered modules cleanly,
including the full assembly, the direct dinaturality proof, and both comparison
statements. The delivery tool also performs its standard declaration axiom probe.

## Proved and sorry left

The original hole `WeilConjectures.coefTowerEvaluationPairing`
(node `lem-coef-tower-evaluation-pairing`) is replaced by complete Lean assembly.
This is a decomposition, not a net proof: one original hole closed, two new holes
added, and zero holes remain in the original module.

The new public theorem `WeilConjectures.coefPairingSystem_dinaturality`
(node `lem-coef-pairing-frame-dinaturality`) is proved from the frame definitions,
projection-map naturality, adjunction naturality and closed evaluation naturality.

Remaining named holes, one per new module:

- `WeilConjectures.coefPairingHomRepresentativeComparison`, node
  `lem-coef-pairing-hom-representative-comparison`.
- `WeilConjectures.coefPairingCompactificationModels`, node
  `lem-coef-pairing-compactification-models`.

These are independent proper parts of the original argument: the first involves
no compactification or pairing, and the second does not assert any representative
Hom computation, integral finite Hom comparison, scalar factorization or
whole-system dinaturality. Each docstring supplies its source and complete proof
plan, with the precise unresolved interface comparisons. Neither statement is the
original theorem under a renamed or repackaged hypothesis: their combination also
requires transport along eQ, isomorphism factorization, and the proved categorical
dinaturality argument.

## No longer needed

The old top-level `tool_uses` approvals are removed from the assembly node; its
proof now uses only the two comparison nodes and the proved frame node. The
underlying results may still be used by those comparisons. Removed entries:

- `lem-pc-kflat-resolution`
- `lem-pur-hom-kflat-into-kinjective`
- `lem-weil-tower-evaluation-kinjective`
- `lem-weil-derived-scalar-extension-restriction-adjunction`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `lem-weil-compact-support-reduction-tower-functor`
- `lem-weil-ringed-tower-pushforward-limit-comparison`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-ringed-slice-extension-exactness`
- `lem-sfb-ringed-derived-monoidal-comparisons`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-sfb-dc-hom-scalar-adjunction`

The direct frame proof replaces the planned use of
`lem-coef-pairing-system-dinaturality` /
`Sheaf.SixFunctors.CoefPairingSystemDinaturality` in this item. It is not imported.
The support/open, scalar-Hom, projection-evaluation and finite-normalization
nodes remain needed by the split comparison lemmas. The fixed trace construction
and all its public imports are retained; no trace or inverse limit occurs in the
assembly. No Lean module is withdrawn and no unit route is changed.

Removed proof imports from the relocated data block (the constructions compile
without these old planned proof dependencies):

- `Sheaf.Paper.CoefficientRingedSequenceSite`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Paper.FiniteCoefficientPoint`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.CategoryTheory.RingedSliceExtensionExactness`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`
- `Sheaf.Paper.SemilinearDerivedSections`

These are only removed direct imports, not assertions that every transitive
module or mathematical result is globally unnecessary. The existing proved data
helpers still use the two retained Mathlib proof imports.

## Where the brief, the DAG or earlier work was wrong

The dependency declarations use the native quotient-ring and quotient-point
interfaces (`CoefProjectionEvaluation.Model`, `ScalarSpecialization` and
`FiniteEvaluation`); the assigned theorem uses the older composed
`CoefPairingFrame` interface and strict constant-R tower sections. Applying the
stated dependencies therefore requires real comparisons of their reductions,
sections, adjunctions, tensor words and finite support, rather than a direct
`exact` of the existing statements. The split lemmas isolate those comparisons.

The given eQ transition condition is not needed for these clauses: target
transition compatibility is handled separately in trace rectification. The
original binder and statement are nevertheless kept verbatim.

Edge cases checked for the new statements: zero input and empty X give zero
pairings; identity and zero morphisms satisfy the categorical dinaturality
calculation; the point with K=R or K=R/varpi retains the R-to-A_n balancing map,
so no flatness of a quotient is assumed. The Hom representative comparison uses
K-injectivity in the target and thus allows arbitrary P, as the original
statement requires. No varying-ring evaluation is assumed to preserve
K-injectives, and no arbitrary data witness is chosen from an existence hole.

## New nodes

`lem-coef-pairing-hom-representative-comparison`: representative and integral
finite-evaluation comparison for the fixed Hom tower, without any compact support.

`lem-coef-pairing-compactification-models`: realization of the specified native
projection word in the fixed frame, with support transitions and finite pairing.
It retains the actual scalar balancing and both ambient projection mates.

`lem-coef-pairing-frame-dinaturality`: proved whole-system frame dinaturality,
without the finite-Tor restrictions needed by the original application.

The existing definition node is attached to the extracted data module; the
original theorem node now records the actual three-step Lean assembly.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
