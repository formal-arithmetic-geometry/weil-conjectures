## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.integral_general_lfp_hom_finiteness`
with a complete Lean assembly. The statement, both existing definitions, and all existing
public imports are unchanged. The assembly uses the declared integral Hom reduction theorem,
with an explicit normalization equality for the canonical comparison, and three separate
presentation lemmas for inputs, completeness, and residue origin.

Added four one-theorem modules and their nodes. Each remaining gap is a public theorem
whose entire proof is `by sorry`, with a source and proof in words. These are coefficient
and localization comparisons missing from the currently declared interfaces, rather than
new copies of the three-part parent theorem.

The proved private helper `boundedEtaleRepresentative` constructs a strictly bounded
representative from cohomology bounds using Mathlib, transports constructibility through
homology of the derived isomorphism, and proves every displayed degree-zero tensor test
from the zero terms of that representative. The final proof transports this representative
through the derived site-comparison functor and composes the residue isomorphism.

The five-module sandbox compiled successfully with `lcompile.py --all`, including the
import cleanup and the use of the original `integralHomReduction` wrapper. All five files
finished within the server's per-file limit; the item took 33.2 seconds.
The earlier missing `MonObj` instance was fixed by opening the existing
`CategoryTheory.Obj` scope, rather than changing any coefficient structure.

## Proved and sorry left

This delivery is a decomposition: one existing hole closed, four holes added, net -3 holes
before any independent progress in the dependencies. It is not a claim of a net proof gain.
The item module has zero `sorry` occurrences.

Closed:

- `AlgebraicGeometry.ProEtale.integral_general_lfp_hom_finiteness`.

Added and still unproved:

- `WeilConjectures.integralHomComparison_normalization`,
  node `lem-sfb-integral-hom-comparison-normalization`, in
  `Sheaf.Paper.IntegralHomComparisonNormalization`.
- `AlgebraicGeometry.ProEtale.integralAdicHom_complete`,
  node `lem-sfb-integral-adic-hom-completeness`, in
  `Sheaf.Paper.IntegralAdicHomCompleteness`.
- `AlgebraicGeometry.ProEtale.integralAdicInput_normalization`,
  node `lem-sfb-integral-adic-input-normalization`, in
  `Sheaf.Paper.IntegralAdicInputNormalization`.
- `AlgebraicGeometry.ProEtale.integralAdicHom_residue_origin`,
  node `lem-sfb-integral-adic-hom-residue-origin`, in
  `Sheaf.Paper.IntegralAdicHomResidueOrigin`.

The normalization theorem asserts equality of two already defined maps at all positive
quotients; it asserts neither invertibility nor constructibility. The completeness lemma
has arbitrary inputs and only completeness of the second argument, with no geometry.
The input lemma is an assertion about a single general-lfp input and the fixed transport.
The residue-origin lemma assumes adic input witnesses and the canonical reduction
isomorphism, and concludes only cohomologically bounded constructible etale origin.
Strict boundedness, the common tensor interval, and their compatibility with that same
origin are proved in the item module.

Edge cases checked against the definitions and source argument: zero inputs and the empty
scheme; torsion integral modules; quotient index zero meaning exponent one; ramified finite
extensions and ell=2; unbounded first argument in the completeness and normalization
lemmas; arbitrary positive-characteristic ground fields different from ell. No finite-field
condition is imposed on the ground field. The auxiliary finite-field datum remains only a
parameter of the legacy reduction API. The private termwise tensor argument works over any
commutative ring; its interpretation as a derived tensor test here uses the residue-field
coefficients already fixed by the original statement.

## No longer needed

Removed these private imports from the item module:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`
- `Sheaf.Paper.IntegralLfpConstantModelComparison`
- `Sheaf.Paper.IntegralCohomologicalAdicCriterion`
- `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`
- `Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.Paper.FiniteFieldInternalHomFiniteness`
- `Sheaf.AlgebraicGeometry.ConstantFieldTorBounds`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`

The item uses the declared input and finite-field witnesses through the new presentation
lemmas, so their internal coefficient preparation and finiteness dependencies remain
needed below those lemmas. Likewise the ringed-site Hom comparison and completeness
theorem remain needed by the completeness lemma. These are removals of direct imports,
not claims that these modules are globally unreachable.

The parent no longer invokes `lem-sfb-constant-field-tor-bounds` or
`det-pe-finite-tor-comparison-noetherian`: the displayed termwise tensor tests follow
directly from a strictly bounded representative. Those nodes remain in the existing
finite-field witness's proof route. No module is withdrawn or claimed globally pruned.

Pruned the parent's obsolete direct `tool_uses` entries, retaining its original approved
`lem-coef-integral-hom-reduction` and `lem-sfb-bounded-representative` in their original
order. Removed entries are `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-locally-noetherian-quasi-separated`,
`lem-weil-l-adic-extension-integers-dvr`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`lem-sf-module-object-ordinary-coefficient-equivalence`,
`lem-sfb-integral-cohomological-adic-criterion`,
`lem-sf-ringed-rhom-derived-complete`, `sk-thm-pe-constructible-comparison`,
`lem-sfb-constant-field-tor-bounds`, and `det-pe-finite-tor-comparison-noetherian`.
Their uses below the new presentation lemmas are recorded in the corresponding nodes.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies exist and have the expected mathematical content, but several
of their Lean interfaces differ from the parent's fixed presentations. In particular,
`generalLfpAdicInputWitness` uses WithAbs lattice coefficients and a termwise transported
representative, whereas the item uses spectral integer coefficients and its fixed derived
composite. The declared ringed Hom completeness theorem uses a small-site localization,
whereas the item first transports an ambient internal-module Hom. The finite-field witness
uses normalized discrete coefficient encodings rather than the item's fixed-scalar residue
complex. These comparisons are the new input, completeness and residue-origin statements.

Also, `integralHomReduction` proves invertibility of `IntegralHom.comparison` for its
normalized presentation records. The item's canonical map is defined using a second
normalized record, with the opposite tensor order. Equality of the two evaluation
transposes requires the normalization lemma; applying an arbitrary endpoint isomorphism
would not prove the required `IsIso` statement.

No mathematical statement was weakened or disputed. The unit's integral route is retained.
The source-library tree was not modified. The blueprint ancestor command returns `None`
for the item because its historical `created.item` chain is broken; the new nodes record
that result and state their exact place in the integral Hom argument explicitly.

## New nodes

`lem-sfb-integral-hom-comparison-normalization` compares the actual canonical maps.
Its proof uses uniqueness of normalized tensor localization, the Koszul exchange,
Hom-complex evaluation, scalar-unit normalization, and injectivity of currying.

`lem-sfb-integral-adic-hom-completeness` is Stacks Tag 099A transported through the
fixed section-action, coefficient, derived-universe and equivalent-small-site comparisons.
It needs no constructibility or boundedness hypothesis.

`lem-sfb-integral-adic-input-normalization` transports the existing single-input general-lfp
witness to the fixed spectral coefficient presentation, using its scalar-normalization
uniqueness clause and exact equivalences. It permits torsion inputs.

`lem-sfb-integral-adic-hom-residue-origin` converts the two given residue models to the
finite-field witness interface and transports the result back through the inverse of the
assumed canonical reduction map. It stops before strict bounded truncation and tensor tests.

All four nodes have the same chapter and unit as the item, three kinds of Mathlib search,
source locations, proofs in words, and verbatim Lean signature attachments. No change
record is required: no existing signature, definition body, or public import changes.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
