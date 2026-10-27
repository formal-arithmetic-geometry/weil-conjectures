## What changed

The original theorem `WeilConjectures.AdicQbarRealization.adic_completed_tensor_realization_descent`
now constructs the unchanged descent record. Its proof obtains residue-field
invertibility and qcqs geometry, applies the existing
`CategoryTheory.ringedDerived_closed_symmetric_monoidal` theorem to the actual
native coefficient sheaf, obtains normalized finite models at every coefficient
field, obtains their common-stage lift, and copies the resulting data and laws
into the original records.

New modules:

- `Sheaf.Paper.AdicCompletedTensorFiniteModels`: finite-model data and predicates;
  the existing tensorStage, tensorIntegralObjectIso and tensorQuotientIso definitions
  are relocated verbatim and publicly reexported by the item.
- `Sheaf.Paper.AdicCompletedTensorFiniteModelExistence`: existence at one finite field.
- `Sheaf.Paper.AdicCompletedTensorCommonLift`: descent of supplied finite models.

The three original finite-normalization predicate signatures are unchanged. Their
bodies are transparent specializations of the same equations in the new data
module. No additional assumptions are added to the original theorem, and none of
its conclusions or normalization clauses is dropped. No source-library file is
changed. The change record is `coord/changes/Q2-adic-completed-tensor-finite-models.md`.

Validation: lcompile.py compiled the original assembly without warnings in 17.1 s;
the finite data, finite existence and common-lift modules compiled individually
in 28.1 s, 4.4 s and 8.1 s. The unchanged direct importer AdicQbarConstructibleRealization compiled against
the packet in 13.1 s, including the newer unpublished dependency overlay. Its
temporary sandbox copy was then removed. The delivery tool will also compile
the final sources with its axiom probes and validate the whole packet.

## Proved and sorry left

This is a decomposition, not a net proof. One original hole is closed and two
strictly smaller holes are added (net minus one by hole count):

- Closed: `WeilConjectures.AdicQbarRealization.adic_completed_tensor_realization_descent`
  (node `lem-sf-adic-completed-tensor-realization-descent`). Its assembly proof is
  complete, including the actual native ambient tensor, all four common coherence
  fields and every finite normalization field.
- Added and left: `WeilConjectures.AdicQbarRealization.completed_tensor_finite_model`
  (node `lem-sf-adic-completed-tensor-finite-model`). This constructs one finite
  normalized cochain and derived comparison. Its conclusion contains no common
  tensorator or common-stage coherence.
- Added and left: `WeilConjectures.AdicQbarRealization.completed_tensor_common_lift`
  (node `lem-sf-adic-completed-tensor-common-lift`). This assumes the fixed ambient
  tensor models and the entire already constructed family of finite comparisons;
  it constructs only the common-stage maps, their coherence and their agreement
  with the supplied finite models.

The item itself has zero remaining textual holes. The packet has exactly two,
both the whole proof of a named public theorem with a source, full proof in words
and matching node. No definition has a hole or chooses data from an unproved
existence theorem. The choice of finite models occurs only inside the proof of
the original Nonempty proposition, and is then shared by both records.

## No longer needed

Removed these unused private proof imports from the original module:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.CompletedPrimitiveCounitComparison`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.NormalizedTensorConstraintTransport`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.Paper.IntegralAmbientOperationModels`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.ScalarExtensionTowerCoherence`
- `Sheaf.CategoryTheory.ScalarLocalizationMonoidal`

Their source arguments remain as planned dependencies of the finite-model and
common-lift obligations where needed; they are not claimed as globally pruned.
The new sorry modules do not preload unused proof imports. No existing module
is withdrawn. The original node's direct proof dependencies are replaced by the
ambient tensor theorem, the residue-unit definition and the two new lemmas.
`lem-sf-adic-finite-realization-cocone` / `Sheaf.Paper.AdicFiniteRealizationCocone`
is no longer needed for this proof: the input R already includes its integral
and common-field normalization, while the geometry is obtained directly from T.
The unit's Verdier-duality route and its coefficient transport steps are retained.

## Where the brief, the DAG or earlier work was wrong

The old global-build error names a bad import of NativeAdicFiniteNormalization;
the rework row records a transitive CoefficientChangeOpenImmersion failure.
The current server queue classifies the item as a one-hole proof item, and the
unchanged source compiles against the current published artifacts. No new import
collision or source-level defect was reproduced. This delivery therefore supplies
an actual proof reduction rather than claiming that rebase/restore alone repairs it.

The original seven-step plan mixes the independent ambient monoidal structure,
one-field chain comparison, and common-field descent. The new decomposition
makes these distinctions explicit. The ambient structure is obtained directly
from an existing theorem, not left as another existence hole. The two remaining
lemmas specialize the existing plan, rather than reasserting the final theorem
under another name. Finite normalized maps are fixed before descent, so the
common-stage obligation has genuinely stronger input data and a smaller task.

Source check: read BS Definition 3.4.10, Lemma 6.5.5 and Remark 6.8.15 in the
local paper, HRS Lemma 7.9, and the Stacks proofs labelled
lemma-pullback-tensor-product and lemma-tensor-product-pullback (07A4/03EL).
Their normalized refinement is explicitly marked as agent-written in the nodes.
Edge cases checked in words: empty X and zero complexes use the same constructions;
identity field extensions use multiplication and insertion of one; ramified
extensions use the specified quotient augmentation without identifying
uniformizers; signed symmetry retains the homogeneous-degree sign; arbitrary
finite model witnesses are fixed by their balanced generators and representative
square, not by an assertion that all natural isomorphisms are equal.

## New nodes

`def-sf-adic-completed-tensor-finite-models` records the finite model and its
balanced/representative predicates, the parameterized integral agreement, and
the three unchanged relocated comparison definitions.

`lem-sf-adic-completed-tensor-finite-model` records the single-field normalized
comparison, corresponding to the original first step.

`lem-sf-adic-completed-tensor-common-lift` records the rational/common-field
passage and the constraint equations for already supplied finite data,
corresponding to the original steps 2--7. Its module also defines the result record.

All inherit the original chapter and unit and carry the original provenance.
Mathlib searches used leanfinder, loogle, grep and leansearch; generic completion,
localization and flat-base-change results did not state these specified maps.
Blueprint duplicate search and direct library/DAG searches found no existing
node for either precise input/output interface. The original native At existence
route cannot be used here because its parent proof already uses this item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLift": "ff0f40fa17a4e35971a44a66a4d678a6572b051e", "Sheaf.Paper.AdicCompletedTensorFiniteModelExistence": "1d0540e3436605bdbbda400c9203c6abb11b21a0", "Sheaf.Paper.AdicCompletedTensorFiniteModels": "c5f8e01c0e737e878997f2f5c62ec19d035201e0", "Sheaf.Paper.AdicCompletedTensorRealizationDescent": "84abaa43729332b81154af1c50310a204667a710"}, "results": {"Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}}, "seconds": 139, "time": "2026-10-28T00:58:48+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
