## What changed

The assigned existence theorem is reduced to explicit finite maps, strict tower
assembly, and a separate derived localization step. Its statement is unchanged.
The only change to the existing module is a private proof import and its proof.
No existing dependency module, target, definition, attribute, or public import is
changed.

`PodTensorFiniteSignedShifts` constructs both finite comparison isomorphisms from
the ordinary reduction shift, Mathlib's two signed total-tensor shifts, and the
ordinary scalar-restriction shift. It also proves preservation of flat-term
K-flat representatives under every integer shift directly from K-flatness.
`PodTensorFiniteSignedShiftLaws` proves the two homogeneous generator formulas,
including the sign `(-1)^(p*r)` and transport between the equal total indices.
`PodTensorSignedShiftTowers` assembles those fixed components into actual strict
tower isomorphisms using only adjacent quotient compatibility. Its record
constructor takes the derived fields as parameters; every other data field is
explicit. Its Generators law follows from the proved finite formulas.

The remaining quotient-square calculation is isolated in
`PodTensorFiniteShiftTransitions`. The remaining extension to the completed
derived tensor, normalized by the supplied signed Roos comparison, is isolated
in `PodTensorSignedShiftDescent`. The assigned proof extracts the two Roos laws
from hD, applies that descent separately on X and Y, and assembles both complete
records and all four requested laws. The tensor reindexing data T and hT are
not needed for this intrinsic construction.

The new construction modules use normal transparency settings. All strict maps
are constructed. The derived fields remain in a named theorem's existential
conclusion; no definition selects arbitrary data from that theorem.

Edge cases: shifts range over all integers, with the native shift isomorphisms
covering zero and negative shifts. At zero shift the displayed sign is one;
shifting the second factor leaves the first degree unchanged in the quotient
square. No boundedness, nonzero section, or nonzero coefficient-ring hypothesis
is used. Both remaining statements retain all good representatives and all
identifications of shifted inputs, rather than choosing a convenient presentation.

## Proved and sorry left

One original hole is removed:
`WeilConjectures.podReindexingTensorSignedShiftModels`, node
`lem-pod-reindexing-tensor-signed-shifts-core-models-r3`.
This is a decomposition, not a completed proof of that hole: two strictly smaller
holes are added, with concrete maps fixed before their statements:

- `WeilConjectures.podTensorFiniteShiftTransitions`, node
  `lem-pod-tensor-finite-shift-transitions`: only the two adjacent quotient-square
  equations for the explicitly constructed finite maps.
- `WeilConjectures.podTensorSignedShiftDescent`, node
  `lem-pod-tensor-signed-shift-descent`: only the derived fields and their Model
  equations for the already constructed strict maps and a supplied lawful Roos
  shift.

These are the only two sorries in the packet. Each is the entire proof of its
public theorem in its own module, with a source and complete proof in words.
The assigned module has zero sorries. Neither new statement repeats its original
existence assertion: neither constructs both strict and derived tensor shifts,
and the finite statement asserts equations on explicit maps rather than the
existence of any model.

Proved without introducing a sorry: `podTensorGoodShift`, both finite comparison
constructions, the private lemmas `finiteShiftLeft_generators` and
`finiteShiftRight_generators`, `podTensorFiniteSignedShiftGenerators`, both strict
tower assemblies, the generic `podTowerIsoOfAdjacent`, and
`podTensorSignedShiftOfDerived_generators`.
The derived assembly `podReindexingTensorSignedShiftModels` has a complete Lean
proof from the two remaining named obligations.

Validation: all six modules compile through lcompile.py in import order.
Finite constructions: 18.5 s; transition statement: 3.7 s; proved generator
laws: 24.6 s; tower assembly: 53.4 s; descent statement: 3.9 s; assigned
module: 6.7 s. The temporary profiler options were removed. The assigned
module retains its original hT binder and references it explicitly, keeping
the signature unchanged while satisfying the unused-variable linter.

## No longer needed

No original import is removed and no module is withdrawn. Two old planned proof
dependencies are unnecessary for this item:

- `lem-pur-kflat-total-tensor-model`
  (`Sheaf.Algebra.Homology.KFlatTotalTensorModel`): preservation of K-flatness
  under shifts follows directly from the native tensor shift and shift-stability
  of acyclicity. Closure under tensor products is not needed for this construction.
- `lem-pod-reindexing-signed-roos-shift`
  (`Sheaf.Paper.PodReindexingSignedRoosShift`): the supplied D already contains the
  two required signed Roos shifts, and hD gives their coordinate laws. Choosing
  independent Roos shifts would not prove the required Model equations.

These removals concern this item's proof route only; the modules may have other
consumers. The definitions and localization infrastructure of
`lem-pur-integral-operations-well-defined` remain needed. No unit or chapter route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial node compressed both actual finite tensor shift construction and
derived descent into a single existence step. The listed total-tensor model and
Roos-shift existence theorem do not themselves provide the normalized fields
needed here. The delivery makes those maps explicit and separates their
remaining quotient compatibility from their derived extension.

Finite coefficient reduction is a termwise functor, but its recorded quotient
transition is selected by a uniqueness theorem. Its shift compatibility must be
proved using its scalar-extension generator characterization; it cannot simply
be assumed definitionally equal after shifting. The remaining transition node
records that step explicitly.

`blueprint_refs.py ancestor` reported no ancestor for the inherited r3 node.
The new records cite the actual blueprint node
`prop-pod-dual-tate-data-compatibility`, whose current proof at Steps 1 and 5 is
the source already cited by the item. The unit sk-def-weil has no realized steps
to alter, and its statement and route stay unchanged.

## New nodes

`def-pod-tensor-finite-signed-shifts` records the concrete finite maps, their
transition and generator predicates, and the proved preservation of good
representatives under shifts. Its construction uses native Mathlib tensor shifts.

`lem-pod-tensor-finite-signed-shift-laws` records the proved homogeneous generator
formulas, for all complexes, levels, degrees, integer shifts and site sections.

`lem-pod-tensor-finite-shift-transitions` records the two remaining adjacent
quotient squares for those fixed finite comparisons. Its proof in words includes
the uniqueness argument for shifted coefficient reduction transitions.

`def-pod-tensor-signed-shift-towers` records the strict tower assemblies, the types
of the derived fields, the record constructor and its proved generator law.

`lem-pod-tensor-signed-shift-descent` records extension of those already fixed
strict maps through the good-complex localization, with the supplied signed Roos
comparison and all representative normalizations retained.

The tower construction factors adjacent-square assembly through the generic
proved constructor `podTowerIsoOfAdjacent`; the large completed-tensor and
constructibility definitions remain locally irreducible as in the original
shift API. No existing definition or transparency setting is changed.

No change record is needed: the packet changes no existing interface or existing
module besides the proof of its assigned theorem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorSignedShiftModels": "f53aff0dd9228d7520b56f9842e49df3fe7a04a9", "Sheaf.Paper.PodTensorFiniteShiftTransitions": "3bb6e0c2e9e4bb58773c9d7bbfc9ecc9250cedff", "Sheaf.Paper.PodTensorFiniteSignedShiftLaws": "40fd90dabaa80614711e034347a5861ee6fe653f", "Sheaf.Paper.PodTensorFiniteSignedShifts": "cec3500c7edb0b53ccd753c428cf47eeb010101f", "Sheaf.Paper.PodTensorSignedShiftDescent": "1e058c72df660650e010598b042f0478bca916e5", "Sheaf.Paper.PodTensorSignedShiftTowers": "126bd945f4d1bc40ecdfb245c7e0cfbaf2e42c2f"}, "results": {}, "time": "2026-10-28T10:48:32+0800", "transitive": 0, "version": 1}
```

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
