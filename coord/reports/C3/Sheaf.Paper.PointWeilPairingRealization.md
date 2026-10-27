## What changed

Preserved the V4 baseline's eight proved helpers and all old declaration signatures.
Moved the shared coordinate block to `Sheaf.Paper.PointWeilPairingCoordinates`,
publicly reexported by the original module, to avoid an import cycle with the new
step statements. Added pairingVector, the old pairingEnd composite before B.

Reduced tensor_existsUnique to existence of a canonical system and equality of
normalized comparison maps. Reduced point_weil_pairing_realization to two distinct
steps: unit/shift/scalar transport and B-free tensor representatives. The main
proof supplies naturality of realization under postcomposition, applies the Weil
equation to B, and uses the realization bijection to pass from representatives to
cohomology. Existing definitions still choose only uniquely determined objects.

Validation: lcompile.py --all compiled all five final modules in dependency order,
with no errors or warnings. An additional declaration audit confirmed unchanged
signatures and bodies for every existing definition and previously proved theorem;
all five node records passed dependency, cycle and signature checks.

Change record: `coord/changes/point-weil-pairing-coordinates-c3.md`.
No existing downstream Lean modules use this interface, according to downstream.py.

## Proved and sorry left

Baseline: three holes. Two upper holes receive complete proofs from strictly
simpler named steps: WeilConjectures.PointWeilPairing.tensor_existsUnique and
WeilConjectures.PointWeilPairing.point_weil_pairing_realization. This is a
DECOMPOSITION, not a net hole reduction: three split-off holes are added.
The private realize_postcomp naturality helper is fully proved.
The eight V4 proved helpers remain proved without reverting any body.

Every remaining hole:

- WeilConjectures.PointWeilPairing.exchange_isIso, unchanged in the item;
  node lem-pod-point-weil-pairing-realization.
- WeilConjectures.point_tensor_normalization_independent, in the new module
  Sheaf.Paper.PointTensorNormalizationIndependent;
  node lem-pod-point-tensor-normalization-independent.
- WeilConjectures.PointWeilPairing.point_weil_transport_unit_shift, in the new
  module Sheaf.Paper.PointWeilTransportUnitShift;
  node lem-pod-point-weil-transport-unit-shift.
- WeilConjectures.PointWeilPairing.point_weil_tensor_representatives, in the new
  module Sheaf.Paper.PointWeilTensorRepresentatives;
  node lem-pod-point-weil-tensor-representatives.

Thus two of three original sorry bodies are replaced, three holes are split off,
and four sorry bodies remain across the packet. No definition contains sorry.

## No longer needed

No module is withdrawn or asserted globally unnecessary. The old generic
lem-trf-field-complex-cohomology-splitting approval is removed from the parent's
tool_uses: V4's projective-single Hom calculation already avoids that route.
All other planned tools remain needed transitively by the new step statements.
The original private imports of PointFibreEquivalence (import all),
ScalarExtensionExactIntrinsic (import all), Mathlib.CategoryTheory.Shift.Localization,
and WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology move to the
coordinate owner, where the preserved proofs use them. They are not globally pruned.
All original public imports remain publicly available through the original module.
The new coordinate module omits the unused public imports
FrobeniusCohomologyTransport and SfWeilSheafComplex. FrobeniusPointTransportNatural and FieldWeilShriekShiftData remain because iota
and pShift use their comparison declarations. Its
PointFibreEquivalence dependency is private (`import all` for the equivalence proof),
and Mathlib.Algebra.Category.ModuleCat.Projective is private because only proofs
need the regular-module projectivity instance. These are local import reductions,
not claims that their modules are globally unused. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The live source refreshed during this session: an initial copy still had eleven
holes, while V4 had already delivered eight helper proofs. The packet was rebuilt
from the refreshed three-hole source and preserves every V4 proof.
No mathematical statement is disputed. Existing specialised Frobenius exchange
isomorphisms use a compatible compactification; the item's exchange_isIso permits
an arbitrary retained SupportModel. No unjustified application to that broader
interface is made, and its existing hole remains explicit.
New statements were checked on zero objects, zero and negative shifts, and arbitrary
rational Weil arrows. The tensor-independence step compares full completed maps
before localization; it does not infer equality from individual finite reductions.

## New nodes

lem-pod-point-tensor-normalization-independent states only equality of two already
normalized tensor maps, leaving existence to the existing canonical-system theorem.
Its module contains one hole with the finite/full-Roos/rational proof in its docstring.

def-pod-point-weil-pairing-coordinates owns the relocated canonical coordinates and
the ordered vector before B. It contains no new hole and no new data choice.

lem-pod-point-weil-transport-unit-shift states the unit, shifted representative and
scalar steps. It mentions no B or tensor pairing and is strictly a part of the argument.

lem-pod-point-weil-tensor-representatives states the inverse-unit coherence and the
ordered vector equation before applying B. It assumes no Weil equation for B and
concludes no scalar pairing invariance; those calculations are proved in the item.

All new nodes inherit sec-poincare-duality/sk-lem-finite and point to the current
blueprint's final smooth-pairing clause. Three kinds of actual Mathlib search are
recorded from searches.jsonl; blueprint and project searches found no duplicate.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
