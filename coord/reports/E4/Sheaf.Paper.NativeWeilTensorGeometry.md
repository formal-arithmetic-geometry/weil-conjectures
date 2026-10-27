## What changed

Restored the quarantined item source and replaced the proof of
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_geometry`. Its signature and all original
public imports are unchanged. No other existing Lean module is changed.

The proof constructs the native underived tensor from the existing `tensorFunctor` and
`tensorIhomAdjunction`. Parameter maps are mates of internal-Hom precomposition; their underlying
maps are proved to be `Mod.tensorLeftMap`. Additivity, the parameterized adjunction, the natural
underlying tensor comparison, and its inverse-adjunction normalization are proved.

The native chain comparison and its homogeneous-summand equation are constructed from the existing
`HomologicalComplex.mapBifunctorComparison` API; no flatness or boundedness is required.

The native derived monoidal structure and symmetry are explicit Mathlib equivalence transports.
The coefficient-unit isomorphism is explicitly composed from the ringed unit, the single-functor
comparison and the underived coefficient-unit comparison. These definitions contain no holes and
select no arbitrary witness from a theorem.

The main proof applies the already declared ringed monoidal theorem twice and the existing
`ringed_forget_tensor_descent` theorem once. It assembles their output with the remaining
representative transport theorem. The final ordinary coefficient-unit isomorphism is constructed
from the coherent unit, and the requested equality is proved by cancellation of isomorphisms.

Two remaining parts are separated: the underived action-site square, and transport of a supplied
ringed `TensorComparison` to the fixed explicit native monoidal structure. The latter takes the
actual descended chain, representative and coherence data as input; it does not assert an
unspecified native monoidal structure or perform ringed descent again.

Validation: all six modules compiled through `lcompile.py`; the complete item proof compiled
in 22.6 seconds after factoring its private assembly helpers. Debug profiling options have
been removed. The delivery command checks the final packet again.

## Proved and sorry left

Original holes: 1, in `native_weil_tensor_geometry`. Its body is now complete Lean.
New holes: 2. This is a decomposition with a net increase of one hole, not a complete proof of the
geometry independent of remaining statements.

Proved: `native_weil_tensor_chain` (node `lem-sf-native-weil-tensor-chain`),
`native_weil_underived_tensor` (node `lem-sf-native-weil-underived-tensor`), its private
mate construction and normalization lemmas, the private `unitNormalization` calculation, and the private assembly lemmas
`geometry_from_comparison` and `geometry_from_bridge`. These helpers keep each formal
assembly step within the existing heartbeat budget; no limit is raised.
The four definitions in `NativeWeilTensorRingedStructure` are explicit and have zero holes.
The bridge record has zero holes.

Every remaining hole is exactly a public theorem body `:= by sorry`:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_bridge`, node
  `lem-sf-native-weil-tensor-ringed-bridge`, in `NativeWeilTensorRingedBridge.lean`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_transport`, node
  `lem-sf-native-weil-tensor-ringed-transport`, in `NativeWeilTensorRingedTransport.lean`.

Both have complete argument descriptions and source references in their docstrings. The first
contains only underived categories and resolution preservation. The second assumes the bridge,
normalized underived tensor, two ringed monoidal structures and the already descended comparison;
its conclusion supplies representative and coherence data for an explicitly fixed native tensor.
Neither is the original theorem under a new name.

## No longer needed

No original public import, module or node is globally pruned. The original Frobenius action-site
resolution dependency remains needed by the lower bridge and representative-transport arguments.
The ringed monoidal and ringed descent dependencies are used directly by the main proof.

Removed redundant exploratory imports: `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor` from
the new underived module, and direct imports of `NativeWeilTensorRingedBridge` and
`RingedForgetTensorDescent` from the item; the latter are available through the required public
signature dependencies of `NativeWeilTensorRingedTransport`.

## Where the brief, the DAG or earlier work was wrong

The underived tensor construction need not be deferred to a new action-site theorem: the source
library already gives its functors and normalized adjunction. The categorical mate glue is proved
here. The original DAG's action-site realization is formulated for the recorded sectionwise
fixed-pair model; its declaration alone does not state the compatible square with the actual
native forgetful functor. That square and its normalized Hom and unit comparisons are isolated
explicitly before any native derived tensor is constructed.

The source was quarantined for an import/build issue; its absence did not justify withdrawal.
This packet restores it with its original statement and attachment. The unit route is retained.
No target, existing definition, source-library declaration, attribute or public import is changed.
Edge cases checked in formulating the lower statements include zero modules, the empty site,
arbitrary unbounded complexes, and K-flat complexes without termwise flatness. The latter condition
is not silently strengthened to flat-term K-flatness in the native presentation.

## New nodes

`lem-sf-native-weil-tensor-chain`: the proved chain isomorphism extending the actual underived
comparison, with its prescribed homogeneous summands on all unbounded complexes.

`def-sf-native-weil-tensor-ringed-bridge`: the underived square, Hom normalization, unit and
flat-resolution data; it asserts no existence and has no hollow field.

`lem-sf-native-weil-tensor-ringed-bridge`: existence of that underived square by the action-site
realization and exact orbit-sum induction. This is a remaining hole.

`lem-sf-native-weil-underived-tensor`: the proved additive native tensor and its normalized
parameterized adjunction, constructed from the existing source adjunction.

`def-sf-native-weil-tensor-ringed-structure`: explicit derived equivalence, monoidal transport,
symmetric transport and coefficient-unit comparison, all constructed without holes.

`lem-sf-native-weil-tensor-ringed-transport`: representative/coherence transport for supplied
ringed descent data on the fixed transported native tensor. This is the other remaining hole.

The existing geometry node's proof, proof dependencies and proof origin now follow the Lean
assembly. The proved chain step uses `lem-pc-total-bifunctor-comparison-iso` as a generic
totalization tool from another unit. Its existing source proof is reused; this does not
replace any step of the original unit route. No maintainer tool approval is edited.
No shared-interface change record or forced adaptation is required.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
