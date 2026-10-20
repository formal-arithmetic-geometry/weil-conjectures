## What changed

The target theorem `CategoryTheory.ringedFiniteFreeHomBaseChange` is proved with its original
signature.  The proof obtains the existing derived change-of-rings cochain model and closed
symmetric monoidal models, then applies the proved tensor and Hom intermediate theorems.
Repair C-fc7ec D1: the coordinate theorem now pins a and aQ on every K-flat
representative by the actual scalar sections of the supplied basis. Its β is pinned
by the expanded scalarHomRestrictedEvaluation transpose equation. Ordinary and derived
adjunctions in that formula are themselves fixed by the 1 tensor x unit and the actual
chain-transpose normalization. Hom extracts the additional clauses; its signature stays
the same. The coordinate docstring and node now state these normalizations explicitly.
Reviewer brief point 6 is repaired: tensor-data's lean.declarations lists only the tensor
theorem, while the unchanged scalar-section definition belongs to tensor-complex/Data.

All five delivery modules were recompiled on the current published build through
lcompile.py --all during this retry: Data 9.2s, Coordinates 23.3s, Tensor 31.4s,
Hom 53.4s, main 39.0s. Every single-file compile passed within 60 seconds.
The five theorem signatures match their DAG lean.statement records verbatim.
The predicate contains no sorry and the original main and Hom signatures remain unchanged.

The retry dry run passed compilation and server preflight (CODEX). Its appended axiom
probes for Hom and Tensor timed out at 60 seconds; deliver3.py reports that the merge
will rerun those probes. The standalone module compiles above passed.

The scalar-section definition is publicly reexported from the Data module to avoid an import
cycle.  The Hom and Tensor intermediate theorems compile without `sorry`.

## Proved and sorry left

This repair closes zero additional holes and adds zero additional holes relative to
returned head fc7ec3275. The retained packet has the same two named holes.

The original target hole is closed.  This is a genuine decomposition: two strictly smaller
intermediate results remain as named public theorems, so the net target-import closure change
is one hole closed and two holes added.

Proved declarations:

- `CategoryTheory.ringedFiniteFreeHomBaseChange`
- `CategoryTheory.ringedFiniteFreeHomBaseChange_tensor`
- `CategoryTheory.ringedFiniteFreeHomBaseChange_hom`

Sorry left:

- `CategoryTheory.ringedFiniteFreeHomBaseChange_complex` in
  `RingedFiniteFreeHomBaseChangeData`, node `lem-sf-ringed-finite-free-tensor-complex`.
  This is the chain-level scalar tensor comparison and preservation of K-flatness.  Its
  docstring gives the pure-tensor construction, differential check, and K-flat argument.
- `CategoryTheory.ringedFiniteFreeHomBaseChange_coordinates` in
  `RingedFiniteFreeHomBaseChangeCoordinates`, node `lem-sf-ringed-finite-free-hom-coordinates`.
  This constructs the specified basis comparison and scalar adjunction and proves the
  coordinate calculation. The basis maps are fixed on all K-flat representatives and β
  by its evaluation transpose, so this is no longer an isomorphism assertion with
  unpinned existential identifications. It intentionally stops before product preservation,
  matrix inversion,
  naturality, and assembly of the final isomorphism.

There are exactly two `sorry` occurrences in the five delivery modules.  The split statements
are strictly smaller than the target and each has a complete source and proof plan in its
module docstring.

## No longer needed

No imported node or module is globally withdrawn.  The main proof does not need direct proof
imports of `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`, or
`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`; the statements and the retained
intermediate modules provide the required interfaces.  The existing public imports are kept
where they are part of the module interface.  No blueprint unit statement or realized proof
step is bypassed, and no module is withdrawn.

The earlier exploratory full proof for the chain-level split is not part of the delivery: the
current source was restored to the compiling named split after the server exposed unresolved
universe and extensionality errors in that exploratory proof.  Consequently this report counts
that theorem as a remaining `sorry` rather than claiming it is proved.

## Where the brief, the DAG or earlier work was wrong

Reviewer C-fc7ec correctly identified that the returned coordinate statement left a,
aQ and β unpinned, allowing β to absorb invertibility of c. The repaired statement adds
explicit component and transpose equations. Rank zero still determines all relevant
maps uniquely; the formulas apply to arbitrary unbounded K-flat representatives.
The tensor-data declaration inventory also wrongly attributed ScalarSection to Tensor;
the inventory is corrected without moving or renaming any declaration.

An earlier Hom intermediate statement allowed arbitrary tensor-preserving data and therefore did
not identify extension along the actual ring map.  It was replaced by the current statement with
the actual object and map equations, universal derived pair, normalized models, and representative
square.  The final proof uses this repaired interface.

The exploratory chain-level proof was also reported as compiling in an earlier continuation, but
that result was not reproducible against the current source and later checks found unresolved
errors.  It is excluded from the delivery and represented by the honest split above.  No target
signature, launcher file, budget file, or blueprint unit was changed.

## New nodes

- `lem-sf-ringed-finite-free-tensor-complex`: chain tensor comparison and K-flat preservation;
  retained as the Data split.
- `lem-sf-ringed-finite-free-tensor-data`: derived tensor comparison by representative descent;
  proved in `ringedFiniteFreeHomBaseChange_tensor`.
- `lem-sf-ringed-finite-free-hom-coordinates`: finite-free coordinate identities; retained as
  the Coordinates split.
- `lem-sf-ringed-finite-free-hom-transpose`: matrix transpose, conservativity, and naturality;
  proved in `ringedFiniteFreeHomBaseChange_hom`.

Change record: `coord/changes/E8-ringed-finite-free-scalar-section-location.md`.

Repair change record: `coord/changes/E8-ringed-finite-free-coordinate-normalization.md`.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
