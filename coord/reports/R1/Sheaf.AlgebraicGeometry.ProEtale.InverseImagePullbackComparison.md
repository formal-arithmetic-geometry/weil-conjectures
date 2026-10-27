## What changed

Filled all eight theorem proofs in
`Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`.
All existing public signatures, attributes, docstrings, definitions, and public imports
are unchanged. Every new construction or auxiliary lemma is private and proved.

Constant-section normalization identifies the finite coefficient transport with the
sheafification compatibility isomorphism. Naturality constructs the coefficient-diagram
isomorphism, and preservation of limits proves the prescribed completed structure map
invertible. Finite exactness applies the existing general
`AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact` through a private import.

The finite comparison is constructed from the actual pullback unit followed by
restriction along the comma arrow. Its linearity follows from the normalized coefficient
map; naturality makes a chain map. The integral comparison first applies the actual
ordinary reduction unit, constructed from `1 ⊗ x`, and then the finite comparison.
The limit projection equation proves completed linearity. The recorded generator formulas
prove strict transition compatibility; product extensionality proves the Roos lift equation.
Exact inverse image preserves the resolution quasi-isomorphism, which localization inverts.

Added the private proof import of
`Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact` and an `import all` of
`Sheaf.Paper.IntegralReductionTowerUnrestricted` to use its proved ordinary-reduction
object/map identifications and pure-tensor naturality. No source-library file was edited.
Updated the two attached completed-coefficient nodes' proof plans to describe these proofs.
The unit statement and every realized step remain in place. Local irreducibility
attributes keep the constant-sheaf, standard-derived-category and completed-coefficient
constructions from being unfolded during instance registration and linting. After the
sectionwise constructions are finished, the final localization instance also keeps the
localization functor irreducible and uses the proved exactness interface.
No global attribute or public definition body changes.

## Proved and sorry left

Closed 8 of the original 8 holes, all in namespace `AlgebraicGeometry.ProEtale`:

- `inverseImageCompletedCoefficientComponent_naturality`
- `inverseImageCompletedCoefficientMap_isIso`
- `inverseImageFinitePullback_exact`
- `inverseImageFiniteComparison_existsUnique`
- `inverseImageReductionTheta_existsUnique`
- `inverseImageReductionTheta_compatible`
- `inverseImageReductionProduct_lift_condition`
- `inverseImageResolution_isIso`

Added holes: 0. Remaining direct holes in the item: 0. Split-off statements: 0.
Validation: `lcompile.py` compiled the complete module cleanly in 43.5 seconds,
with no warnings, on 2026-10-26. No profiling or trace options remain.
The proof uses the existing declared dependency theorems; this does not claim that their
entire transitive axiom closure is already free of sorry.

## No longer needed

No modules or nodes withdrawn; no imports removed. The original public imports retain
the existing interface. No new finite-exactness development is needed here: the existing
general coefficient pullback exactness theorem supplies it. The constant-map and
limit arguments follow the unit route, with no change to its realization. The explicit
coordinatewise inverse in the completed-map node's former proof plan is unnecessary:
`preservesLimitIso` and `HasLimit.isoOfNatIso` give that inverse abstractly. All its
constant-sheaf, sheafification, site-equivalence and inverse-limit definition nodes
remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The two attached nodes received reviewed
stage-1 statements during this proof session. Those current reviewed statements and their
metadata are preserved; only the proof plans, proof dependencies and proof origins are
updated. The proof sources are the Stacks tags already documented on the declarations.
The natural-number index remains the positive exponent n + 1; the proof imposes no bound,
constructibility, completeness, or equality of site/coefficient universes. The constructions
also apply to n = 0, the identity isomorphism, zero complexes, and empty schemes.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
