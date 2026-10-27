## What changed

Replaced the original sorry in `etale_ringed_projection_identification` by a Lean
assembly of the geometric realization, native ordinary tensor realization,
normalized corner constraints and native derived comparison. The original theorem
signature is byte-for-byte unchanged. No target or existing definition changed.
No adopted source-library declaration was edited.

The item itself constructs the normalized `RingedTensorModel` on each corner:
its representative natural isomorphism is the inverse localization lax tensorator.
Naturality is proved by cancelling the two invertible tensorators in lax naturality.
Normalization is their hom-inverse identity. It also constructs `NativeTensorData`
from the proved generic exact braided-equivalence derived comparison and K-flat
preservation results in ConstantScalarRestrictionTensor. These constructions are
not new existence holes, and no definition chooses unspecified data from a sorry.

The three realization/comparison components have distinct hypotheses and conclusions.
The geometric component contains no derived tensor data. The ordinary tensor
component concerns one site and contains no morphism or derived category. The
native derived component assumes all the ordinary geometric and normalized corner
data, and proves their comparison with the published derived functors and projection.
The constraints component is the independent associator/Koszul descent argument.
Each is sourced and attached to a new DAG node. All new imports are proof imports.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Etale.RingedProjectionIdentification.etale_ringed_projection_identification`
is closed by the complete assembly. This is a decomposition, not a net proof of
its dependency closure. The item module has zero sorry occurrences. The private
lemmas `localizationTensor_isIso`, `inverseTensor_naturality`,
`normalizedRepresentative_exists`, `normalizedModel_exists` and
`nativeTensorData_exists` are proved without new holes.

Remaining new holes (full namespace above):

- `etale_ringed_geometric_realization`, node
  `lem-pur-etale-ringed-geometric-realization`.
- `etale_ringed_native_tensor_realization`, node
  `lem-pur-etale-ringed-native-tensor-realization`.
- `etale_ringed_native_derived_comparison`, node
  `lem-pur-etale-ringed-native-derived-comparison`.

- `etale_ringed_normalized_constraints`, node
  `lem-pur-etale-ringed-normalized-constraints`.

Count: one original hole closed, four distinct lower holes added. This is a
four-component decomposition, net minus three holes, not a dependency-closure proof.
The inverse-tensor associativity, inverse-tensor braiding and total-constraint
implementation equalities were checked separately during development, but the
concrete dependent TensorConstraints assembly remains in its named lower theorem.
No partial proof or private declaration with sorry is delivered.

## No longer needed

No existing library module is withdrawn or declared unreachable. The arbitrary-ring
statement cannot use the finite-coefficient
`constant_module_derived_projection_identification` by specialization: its `Finite`
hypothesis would be an extra target hypothesis. Its generic private exact-equivalence
helpers remain useful for the new derived-comparison item.

The item does not import new modules for native derived tensor-data existence or
normalized representative-model existence: both are proved directly. No arbitrary
monoidal or representative-model existence theorem is introduced.

Original public imports are preserved. The item's direct proof dependencies are now
the new four components and the proved generic results in
`lem-sfb-constant-scalar-restriction-tensor`; original resolution, adjunction,
ordinary tensor and projection dependencies remain needed through the new
components. Thus moving those dependencies below the components is not reported as
pruning them. No source-tree declaration has been removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The native finite-ring
comparison is not an arbitrary-ring comparison. The explicit lifted-site native
transport requires ordinary tensor and constant-unit normalization; a bare site
equivalence alone does not provide those equations.

Lean elaboration required keeping the expensive sheaf monoidal construction from
unfolding and supplying the existing Grothendieck, closed and flat-resolution
structures explicitly. The main assembly uses sequential existential refinement
so it checks within the unchanged server wall-time limit.

The mechanical blueprint ancestor is null, as already recorded on the parent:
the created-item chain stops at a module name. The new nodes retain its documented
textual provenance in the final paragraph of prop-asd-smooth-base-change and the
tensor-reassociation sentence of prop-sf-pf-coherence. Unit `sk-prop-sf-cbc` has
no realized nodes; this packet changes neither its statement nor its proof route.

## New nodes

`lem-pur-etale-ringed-geometric-realization`: actual ordinary scalar-extension datum
realizing the transported geometric and fixed-scalar adjunctions, with exactness
and the ordinary Hom-normalized scalar comparison. Edge cases checked against the
source construction: zero coefficient ring, identity morphism, arbitrary scheme
morphism; no properness or boundedness is used.

`lem-pur-etale-ringed-native-tensor-realization`: the braided ordinary tensor
structure on literal scalar restriction followed by site transport, normalized on
local pure tensors and constant units. The sheafification universal property fixes
the map, also for zero coefficients and the empty-site case.

`lem-pur-etale-ringed-normalized-constraints`: canonical derived associator and
Koszul braiding for an already normalized corner model. The representative argument
retains all integer bidegrees, including the negative sign in degree (1,1).

`lem-pur-etale-ringed-native-derived-comparison`: localization and K-injective
comparison for prescribed ordinary data and tensor models, including equality with
the canonical edge tensor comparison and the published projection square. The
projection morphism is never assumed invertible. The source computation uses the
same inserted scalar one in each bidegree and the same counit adjunct.

All new nodes inherit the parent chapter and unit and record the actual searches.
No change record or forced adaptation is required: no existing statement or
non-theorem body changed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
