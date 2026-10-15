## What changed

Withdraw the redundant `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinatesFamily`
wrapper. Its only direct user, `QCohOrdinaryTensorResolutionCoordinates`, now chooses
F -> N[0] with `CochainComplex.exists_isKFlatResolution`, defines c_U using the existing
`AlgebraicGeometry.tensorResolutionCoordinateSections`, and applies the existing
`AlgebraicGeometry.tensorResolutionCoordinateSections_naturality` to the supplied
comparison maps. This replaces the witness-and-homotopy route with a direct application.
The parent's public signature, public imports and visibility are byte-identical.

The second reader withdrew all eight first-draft chart modules and their eight nodes:
they duplicated an existing construction and naturality obligation. No new Lean
module, definition, theorem, or hole is delivered. The existing naturality theorem
gets a DAG attachment so that the parent's actual dependency is explicit.

## Proved and sorry left

Holes closed by this delivery: none. Holes added: none. Split-off statements: none.
The originally assigned declaration
`AlgebraicGeometry.qcoh_ordinary_tensor_resolution_coordinates_witness` had already
been decomposed by a concurrent T4 landing. Its retirement is pruning, not a proof.

The parent `AlgebraicGeometry.exists_qcoh_ordinary_tensor_resolution_coordinates`
has a complete new proof term, but still depends on the existing open theorem
`AlgebraicGeometry.tensorResolutionCoordinateSections_naturality`, held by T3,
now attached to `new-g2-existing-qcoh-tensor-resolution-coordinate-naturality`.
The delivery contains no direct `sorry`. The draft's added hole
`AlgebraicGeometry.QCohTensorChart.coordinates_naturality` is not delivered.

Independent scratch `#print axioms` checks give only `propext`, `Classical.choice`,
`Quot.sound`, and the expected `sorryAx` for the parent. The existing coordinate
construction and `CochainComplex.exists_isKFlatResolution` use only the three
permitted axioms. No definition chooses arbitrary data from an unproved existence
statement: F and s are chosen inside the theorem proof from a proved existence theorem.
The pinned sorry ledger, rather than this wrapper removal, determines global progress.

## No longer needed

Removed parent proof imports:

- `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinatesFamily`
- `Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy`

A source import-closure comparison finds these three Sheaf modules removed from the
parent's route: the two above and
`Sheaf.AlgebraicGeometry.QCohTensorResolutionSecondKFlat`. The last is a proved
convenience wrapper; the proof calls its underlying K-flat existence theorem directly.
Only the family module is withdrawn from the library; the other two remain available
to their other users.

Removed unused private helpers: `semilinearTensorLift`, `semilinearTensorLift_tmul`,
and `semilinear_tensor_resolution_lift_homotopy`.

Every old parent `proof_deps` entry is retired:
`new-j1-qcoh-ordinary-tensor-resolution-coordinates-witness` and
`new-t4-augmented-resolution-lift-homotopy`. The generic homotopy module is retained
elsewhere; only the family wrapper is withdrawn by this delivery. Its node's statement
is preserved and its unused Lean attachment is set to null.

The draft's eight `QCohOrdinaryTensorChart*`, `QCohOrdinaryTensorDerivedComparison`,
`QCohOrdinaryTensorRestriction*`, and `QCohOrdinaryTensorSemilinearTilde` modules and
corresponding `new-g2-qcoh-ordinary-tensor-*` nodes are withdrawn from this delivery.
They are not claimed as existing-library modules pruned. The earlier claim that 15
existing modules leave the parent's route is withdrawn: the final proof deliberately
reuses the existing coordinate chain. Its underlying affine comparison modules and
existing naturality hole remain imported.

The unit `sk-thm-picard-duality` and its `realized` fields are unchanged. The proof
retains affine tensor computation and restriction naturality. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's route reproduced the existing coordinate construction and replaced
its existing naturality hole by a duplicate new hole. Local source search found
`tensorResolutionCoordinateSections_naturality`, which already asserts precisely the
required equation for every supplied comparison. Reusing it removes that duplication.
The family wrapper was concurrently proved by decomposition before this review;
no closure is attributed to deleting it.

No DAG node attached the existing fixed-coordinate naturality theorem. The delivery
adds a metadata-only attachment. Its source docstring cites two unavailable helper
names, `tensorResolutionChartTensorIso_naturality` and
`tensorResolutionCoordinateSheafIso_naturality_of_squares`. The new node describes the
mathematical tensor and homology squares without treating those names as proved lemmas.
The existing source is held by T3 and is not modified. Its open obligation is disclosed.

Independent LeanFinder, Loogle and Mathlib source searches found general tensor and
homology naturality APIs; the precise coordinate theorem was found in `lean/Sheaf`.
The cited Stacks affine computation (08DX), K-flat tensor comparison (06YT), affine
pullback (01I9) and tensor pullback (01CD) support the existing coordinate route.
No new statement is introduced merely to restate the assigned item.

## Forced adaptations

`Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates` was unclaimed at
12:12, 2026-10-15. A counterfactual local compile of its original source against the
empty family module independently reproduced:

```text
QCohOrdinaryTensorOriginalParent__probe.lean:212:20: error(lean.unknownIdentifier):
Unknown identifier qcoh_ordinary_tensor_resolution_coordinates_witness
```

The adapted parent compiles. Replacing its proof import and final proof is necessary
when withdrawing that witness. Its obsolete private homotopy helpers are removed.
The public signature and visibility remain identical. No held module is adapted.
The interface withdrawal is declared in `coord/changes/qcoh-direct-coordinate-parent.md`.

## New nodes

`new-g2-existing-qcoh-tensor-resolution-coordinate-naturality` attaches the existing
`AlgebraicGeometry.tensorResolutionCoordinateSections_naturality` in
`QCohTensorResolutionCoordinateSectionsNaturality`. It states naturality of the fixed,
constructed coordinates under supplied augmented semilinear tensor comparisons.
Its Lean signature is copied verbatim, with a complete mathematical proof plan and
search record. It adds no Lean declaration or hole. The parent node's proof and
proof_deps now name this theorem and `lem-pc-kflat-resolution`; the family witness
node loses only its Lean attachment.

## Second reading by G2

1. Compared delivered existing sources and nodes with the repository. The parent's
   theorem signature, public imports and visibility are byte-identical. The sole
   withdrawn public declaration is the family witness, explicitly declared in the
   change record. A whole-library source search found only the adapted parent as
   its direct user. No target signature or existing data definition changes.
2. Read the parent, family, coordinate construction, naturality statement and K-flat
   replacement, and the first draft's supporting modules. The final parent compiles
   without warnings. Scratch axiom checks show only the permitted axioms and the
   disclosed existing naturality `sorryAx`; the constructed coordinates and K-flat
   existence theorem themselves have no such dependency. No direct sorry, hollow
   definition or forbidden implementation escape is delivered. The counterfactual
   original-parent failure was independently verified.
3. There are no new split-off statements. Checked the reused naturality statement
   on n=0, zero coefficients, zero rings, empty affine opens and identity restriction;
   the tensor, augmentation and exact-homology equations require no extra hypotheses.
   It applies for arbitrary supplied comparisons and unbounded K. It asserts an
   equation for fixed constructed coordinates, rather than existence of the family.
   Source and library searches found this existing obligation and avoided duplicating it.
4. Replaced the entire duplicate chart route by the direct application of existing
   coordinate naturality. Removed all eight new modules, eight nodes and their added
   hole from the draft, as well as the parent's obsolete homotopy helpers and imports.
   The pruning list names both old proof dependencies and distinguishes route pruning
   from global hole closure. The unit and its realized route are unchanged.
5. Checked literal Lean signatures, node proof steps, dependency unions, source,
   searches and blueprint provenance. Existing node statements are unchanged. The
   new metadata-only attachment points to the actual existing theorem, and the
   parent's proof and proof_deps follow the final Lean proof. The witness node loses
   only its Lean attachment. The report discloses the remaining existing obligation.

Second reading changed the proof to reuse existing coordinate naturality, withdrew the
duplicate draft and its hole, removed obsolete imports and private helpers, and corrected
the DAG, change record, pruning inventory and progress accounting.
