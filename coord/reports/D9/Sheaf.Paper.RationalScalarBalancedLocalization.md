## What changed

Only `Sheaf.Paper.RationalScalarBalancedLocalization` and its theorem-owner DAG node change.
The public statements, definitions, instances, public imports and mathematical objects are
preserved. The integral-normalization declaration is moved before the coefficient square so
that the square can use its existing pointwise formula.

The continuity proof reuses `WeilConjectures.integralScalar_absoluteValue` and the isometry
criterion. Integral coefficient compatibility uses finite projections and the inverse-limit
universal property. Constant sections are computed through the sheafification adjunction,
which proves the section and reciprocal formulas even on empty objects. The coefficient
square combines the existing integral normalization with the two inclusion normalizations.

The fraction theorem is proved by an equality in the raw localized Hom module, before either
realization functor is applied. It cancels only units in that localized module, retaining all
integral Hom torsion. The arbitrary-derived-morphism naturality theorem identifies its
components with the canonical comparison of left adjoints. A private category lemma
transports the raw tower equation through the published normalization isomorphisms. The
identity equation is transported by cancelling the specified tensor-unit isomorphism.
The existence-and-uniqueness theorem follows from the specified component naturality by
`NatIso.ofComponents` and extensionality.

The geometric integral normalization is proved from the finite and integral normalization
fields of the two supplied realizations. Finite normalization identifies their maps with the
canonical constant-sheaf comparisons. Their pullback squares give all residue projections;
joint monicity gives the completed square. This specializes the existing proof pattern in
`RealizationCoefficientSquare` without adding a different realization or an existence choice.

Validation: the complete module compiled in 43.2 seconds. A signature comparison confirms
that all 26 public declarations and the public import list are preserved. The only subsequent
Lean edit removes the compiler-reported unused `Category.assoc` simp argument; delivery
runs the final compilation and preflight checks.

New proof imports expose the existing private finite-coefficient projection lemmas from
`PbcScalarExtension`, the canonical adjunction comparison, and the continuous coefficient
completion and pullback APIs. All added helper lemmas are private and proved.

## Proved and sorry left

Closed 12 of the original 18 theorem holes; added 0 holes and split off 0 statements.
All names below have namespace `AlgebraicGeometry.Scheme`.

Closed:

- `rationalBalancedEmbedding_continuous`
- `rationalBalancedIntegralCoefficients`
- `rationalBalancedCoefficient_sections`
- `rationalBalancedCoefficient_square`
- `rationalBalancedFractions`
- `rationalBalancedCoefficient_comp`
- `rationalBalancedNormalizedTower`
- `rationalBalancedGeometricSquare`
- `rationalBalancedGeometricNormalization`
- `rationalBalancedDerivedNaturality`
- `rationalBalancedNormalizedIdentity`
- `rationalScalarBalancedLocalization`

The following six existing holes remain, each attached to
`lem-per-rational-scalar-balanced-localization`, with its existing source and proof docstring:

- `rationalBalancedIntegralNormalization`
- `rationalBalancedComponent_naturality`
- `rationalBalancedTensorModels`
- `rationalBalancedTower`
- `rationalBalancedPentagon`
- `rationalBalancedIdentity`

Some closed theorems still use these existing unfinished declarations. In particular, the
coefficient square uses integral normalization, the two normalized coherence laws use their
raw laws, and the final uniqueness statement uses component naturality. No new hole merely
renames any of these statements, and no definition contains a postponed proof body.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`

The proofs supplied here do not use their declarations directly. The corresponding DAG
nodes still belong to the proof plans for the six retained holes, or remain reachable through
other imports; none is withdrawn and no entire module is claimed pruned. In particular, the
fraction theorem needs no semilinear extension theorem: both functors preserve an equality
already proved in the source raw localization. The updated node records this shorter route.
The unit's realized statement and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. The original eight-step mathematical plan is retained
for the unfinished clauses. Its fraction step can be shortened to cancellation in the source
localized Hom module. Its continuity and derived-naturality clauses already have the needed
normalization APIs in the library. The main existential theorem asserts uniqueness for the
specified components, so once their naturality is available its assembly needs only
extensionality; its companion theorem obligations are retained explicitly.

The import-direction checker once encountered a concurrently disappearing unrelated source
file. Re-running the read-only check succeeded; no tool or shared source was modified.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
