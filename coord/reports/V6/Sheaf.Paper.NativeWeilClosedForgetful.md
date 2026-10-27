## What changed

Reduced AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful to two strictly
smaller native assembly obligations. The derived triangulated instance, derived
conservativity, cohomology comparison, and bounded constructibility are proved
from the existing exact-functor APIs, DerivedCategory.isIso_iff, and K.property.

Sheaf.Paper.NativeClosedTransposition proves nativeBidual_natural,
nativeComparison_evaluation, and nativeComparison_bidual explicitly by uncurrying,
using evaluation naturality, braiding naturality, the normalized Hom comparison,
and invertible tensor/Hom comparisons. These proofs require no new holes.

The pre-existing interfaces are moved verbatim into NativeWeilClosedModels and
publicly reexported from the original module. This makes the two new obligations
independent of the theorem they prove. Change record:
coord/changes/V6-native-closed-model-extraction.md.

## Proved and sorry left

Closed the one original hole: AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful.
This is a decomposition, not a net proof: two holes are added, one in each new module:

- AlgebraicGeometry.ProEtaleWeilSheaf.native_row_hom_comparison
  (lem-sf-weil-native-row-hom-comparison).
- AlgebraicGeometry.ProEtaleWeilSheaf.native_tensor_transport
  (lem-sf-weil-native-tensor-transport).

No sorry remains in the item or in NativeWeilClosedModels or NativeClosedTransposition.
The existing native_two_injective_hom_model is used, unchanged, from the recorded
ringed two-injective dependency. Its sorry is not added by this delivery.

## No longer needed

The item no longer needs the action-site realization to prove derived exactness,
conservativity, cohomology commutation or bounded constructibility. Those follow
directly from the existing native exact forgetful functor. The action-site result
remains needed by native_tensor_transport; it is not withdrawn or globally pruned.

The old public imports now reside in NativeWeilClosedModels and are publicly
reexported, so no old public import is pruned. No existing module is withdrawn.
The closed symmetric monoidal and tensor-Hom adjunction nodes remain dependencies
of native_tensor_transport. The original proof route's resolution, derived tensor
descent and quasi-isomorphism tools remain below the two obligations. No global
module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG assembly treats standard-sign ringed Hom models and native row-sign
product-total models as immediately interchangeable. Their actual interfaces need
an explicit sign conversion and native/ordinary localization comparison. The
Frobenius action result is stated on its small-site fixed pairs, whereas this item
uses the adopted internal module-object category. Tensor and normalized adjunction
transport across that presentation is therefore genuine remaining work, now named.
The unsigned normalization from the landed R4 repair is preserved exactly.

The new statements were checked on zero objects, empty schemes, the point with
trivial action, and even/odd degree parity. The sign conversion is (-1)^(n*p),
its square is one, and it commutes with additive forgetting. The tensor transport
fixes the supplied Hom models and comparison; no arbitrary witness defines data.
Bidual naturality and compatibility use no reflexivity or invertibility of biduality.
The unit record sk-prop-sf-biduality-general has no realized statement/step bindings;
the same native internal-Hom/evaluation/transposition route is retained.

## New nodes

- def-sf-native-weil-closed-models records the verbatim extracted definitions.
- lem-sf-native-closed-transposition records the fully proved formal consequences.
- lem-sf-weil-native-row-hom-comparison records the native/ordinary row-sign conversion.
- lem-sf-weil-native-tensor-transport records tensor and normalized adjunction transport
  onto fixed row-sign representatives.

The parent proof, proof dependencies and declaration attachment are updated.
The new node graph has no missing dependencies or cycle. The original declarations
were compared byte for byte after extraction. All delivered Lean lines are at most
100 characters. Both new obligation modules and the fully proved categorical helper
passed the remote single-file compiler; the complete packet is checked by delivery.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
