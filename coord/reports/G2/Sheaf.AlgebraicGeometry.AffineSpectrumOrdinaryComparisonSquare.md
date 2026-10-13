## What changed

Replaced the sorry in
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_ordinaryComparison_square`
by a reduction to two independent parts of the recorded argument. The generic algebra module
`Sheaf.Algebra.Homology.BaseDerivedTensorRingIsoNaturality` states localized derived tensor
naturality under compatible ring isomorphisms. The ordinary geometry module
`Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoordinateTransport` states the four stalk ring
coordinates, their input and tensor chain isomorphisms, and ordinary pullback stalk compatibility.
Its ordinary homology transport is an explicit composition of existing isomorphisms.

The algebraic theorem forgets scalars after constructing its linear transport. The original
module combines the statements by cancelling exact
restriction homology isomorphisms. A proved private helper evaluates the localization lift
at Q(Pg), cancels the coordinate pullback counit, and identifies the ordinary homology transport.
Naturality of comparisonStalkHomologyIso for the inverse ordinary composition map then gives
the unchanged target square. The definitions, all existing signatures, and all existing public
imports are preserved. Only proof imports and proof helpers are added.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_ordinaryComparison_square`
(node `lem-pc-affine-spectrum-ordinary-comparison-square`). This is a decomposition,
not an axiom-free proof: one upper hole is closed and two strictly smaller holes are added.
There is no sorry remaining in the original module and no sorry in any definition.

New holes:

- `ModuleCat.exists_baseDerivedTensor_ringIso_square`
  (`lem-pc-base-derived-tensor-ring-iso-naturality`): an algebraic statement about arbitrary
  compatible ring isomorphisms, independent of schemes, stalks, ordinary pullback composition,
  and the derived scheme pullback counit.
- `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_coordinates`
  (`lem-pc-affine-spectrum-tensor-coordinate-transport`): a statement about stalk rings and
  ordinary complexes, containing no derived tensor cohomology source or comparison counit.

Both holes have whole-theorem sorry proofs, sources and complete proof descriptions.
The edge cases checked are zero rings, zero complexes, identity coordinate changes, and empty
schemes (where a point of the spectrum cannot be supplied). No K-flatness or comparison
invertibility is needed. The two parts are combined by an actual categorical proof in the item.

## No longer needed

No existing public import is removed and no entire module is pruned. The theorem
`exists_comparisonSourceIso` in `Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport`
is not used in this ring-coordinate reduction: it changes complexes in a fixed square.
That module remains needed for the existing stalk functors and homology factors, and for
other declarations in the targets' closure. The node `lem-pc-stalk-comparison-source-transport` remains a dependency for its
stalk homology definitions and naturality theorem; only its source-transport theorem is unused. The ordinary pullback-stalk dependency
is transferred to the new ordinary coordinate node, not pruned from the argument.
The unused Arrow import was omitted from the new coordinate module.
The redundant `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` import
was removed from the new algebra module; its model import already exports it.

The following old direct `proof_deps` are no longer direct proof steps of the item:

- `def-pc-base-derived-tensor-cohomology-model`: used through the new ring-naturality node.
- `def-pc-single-complex-base-change-stalk-condition`: used through the coordinate node
  and the unchanged comparison definitions.
- `lem-weil-pbc-module-stalk-pullback`: used through the coordinate node.

All three remain in the argument transitively; none is claimed as a pruned module.

## Where the brief, the DAG or earlier work was wrong

The recorded source transport theorem supplies transport between complexes on one fixed
square. Its signature does not identify different stalk rings on the original and spectrum
squares. The new algebraic theorem makes this missing change-of-rings step explicit.
No existing statement is disputed or changed, and the unit's route is preserved.

Mathlib searches were run with LeanFinder, Loogle, grep and LeanSearch; LeanSearch returned
an Internal Server Error and is recorded as unavailable. The available searches found
isoSpec naturality components, not either full intermediate theorem. Blueprint searches
for affine spectrum, stalk, ring isomorphisms, change of rings and derived tensor found
no blueprint statement of either intermediate result. The ancestor tool reports no ancestor
for the item; the new nodes retain the ancestor already recorded on its blueprint.from field,
`lem-pc-rf-perfect-base-change`, and specify the affine-reduction steps they serve.

## New nodes

`lem-pc-base-derived-tensor-ring-iso-naturality` separates the derived algebraic part. It
supplies an additive source isomorphism and localized comparison square from compatible
ring equivalences and a prescribed pure-tensor chain map. Its Lean module is
`Sheaf.Algebra.Homology.BaseDerivedTensorRingIsoNaturality`.

`lem-pc-affine-spectrum-tensor-coordinate-transport` separates the ordinary geometric
part. It supplies the ring equivalences, the input and tensor chain maps, the pure-tensor
formula needed by the algebraic theorem, and the ordinary target compatibility. Its Lean
module is `Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoordinateTransport`.

No change records or forced adaptations are needed: no existing interface changes.

## Second reading by G2

1. I compared the delivered original module with `sheaf-dag`. Existing definitions and theorem
signatures are unchanged byte for byte; the target statement is unchanged. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`. There are no compiler errors,
no forbidden declarations, no `sorry` in the item, and the two split-off `sorry`s occur only as
whole named theorem proofs with matching nodes. Verdict: pass, with the two stated split holes.

3. I checked both split-off statements against their proofs and sources. The ring theorem is the
algebraic derived comparison under four compatible ring equivalences; the coordinate theorem is
the ordinary stalk and chain-map transport. They are strictly smaller than the target and do not
restate it. Mathlib and library searches found only component lemmas. Verdict: pass.

4. I checked the route from the target downward. The proof uses the two new nodes, then the
existing tensor-pullback, stalk-homology, and source-transport declarations. The private
categorical helpers only cancel and compose displayed isomorphism squares. The redundant
`ChangeOfRingsExact` import was removed. Verdict: pass; no module is pruned.

5. I checked the DAG node proof steps and dependencies against the delivered proof, and verified
the unit record is not altered. The old direct dependencies transferred transitively to the two
new nodes and remain mathematically present. Verdict: pass.

The second reading changed only the redundant import in the new algebra module, extra blank
lines in the item, and this report (including the previously incomplete list of old direct
dependencies). I did not rewrite the valid proof or change any statement or definition.

The explicit `#print axioms` scratch check reports only `propext`, `Classical.choice`, and
`Quot.sound` for both original definitions and the new ordinary homology isomorphism. The two
new theorems and the target additionally report `sorryAx`, as expected for this decomposition.
There are no additional axioms.

I independently checked edge cases: identity ring changes reduce the algebra theorem to model
independence and input-isomorphism naturality; a zero input complex has zero derived and ordinary
homology in every degree; a zero coefficient ring has only zero modules. On empty spectra the
coordinate statement is vacuous because it requires a point. In the identity-coordinate case,
the ordinary square is the naturality of the canonical pullback composition mate. The
pure-tensor requirement rules out an arbitrary target automorphism. Both complete docstring
arguments supply the needed exact equivalences and generator equations; neither asserts an
invertible comparison or introduces a flatness assumption.

Additional independent searches used LeanFinder for exact-equivalence conjugation of derived
scalar extension and for stalk tensor-pullback composition, Loogle for
`restrictScalarsEquivalenceOfRingEquiv`, and grep for `stalkMap_comp`,
`restrictStalkNatIso`, and `extendScalarsComp`. I also read the existing localized model
independence and quasi-isomorphism comparison proofs. They cover fixed rings, whereas this item
changes four rings; they are components, not replacements for the new algebra statement.
Neither complete split-off theorem is short enough to close during a bounded review repair.
