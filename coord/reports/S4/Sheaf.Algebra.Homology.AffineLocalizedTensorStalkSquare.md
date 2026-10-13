## What changed

Replaced the sole `sorry` of `Sheaf.Algebra.Homology.AffineLocalizedTensorStalkSquare`
with a complete Lean proof from the algebraic scalar-localization square and the
exact affine stalk scalar-extension coordinates. Both new imports are proof-only.
The existing theorem signature, universes, public imports, and definitions are unchanged.
The existing unused local `let T` remains in the signature; a local unused-variable
linter option permits retaining that signature without a warning.

Added `Sheaf.Algebra.Homology.AffineStalkScalarExtensionCoordinates` and proved
`AlgebraicGeometry.exists_affineStalkScalarExtensionCoordinates`. The proof constructs
the termwise scalar-extension/stalk isomorphism from `IsLocalizedModule.isBaseChange`,
proves its numerator formula and naturality, constructs its chain isomorphism and
fraction-to-tensor equivalences, proves composition compatibility of exact homology,
and identifies the resulting homology map with the existing
`affineTildeHomologyLocalization`. All private helpers are proved. No data are
chosen from a new unproved existence theorem.

Added `Sheaf.Algebra.Homology.AffineScalarLocalizedTensorSquare` with the remaining
algebraic model-localization square as one public named theorem. Its target is the
homology of scalar extension to the fourth stalk, before the stalk of tilde of the
ordinary target. Its source is scalar extension, before fraction coordinates.
It supplies no exact tilde/stalk homology coordinate equation: that substantial part
of the original argument is proved in the other module. The top-level proof
normalizes the new algebraic chain map, composes source equivalences, and uses the
proved naturality equation and `homologyMap_comp` to combine the two arguments.

Updated the item's node and added two nodes to match this proof route. The unit
`sk-thm-picard-semicon` has no realized statement or step binding for this item;
its route and statement are unchanged. No existing module was adapted.

All three delivered modules compile without warnings through `lcompile.py --all`.
The coordinate theorem uses a local heartbeat allowance for the large exact-homology
instance transports; its checked compile stays below the 60-second file limit.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_affineLocalizedTensorStalkSquare`
(node `lem-pc-affine-localized-tensor-stalk-square`). There are no `sorry`s left
in the item's module.

Also proved the new theorem
`AlgebraicGeometry.exists_affineStalkScalarExtensionCoordinates`
(node `lem-pc-affine-stalk-scalar-extension-coordinates`) and all five private helpers
in its module. It introduces no holes.

Added one hole, and this is every remaining `sorry` in the delivered Lean files:
`AlgebraicGeometry.exists_affineScalarLocalizedTensorSquare`
(node `lem-pc-affine-scalar-localized-tensor-square`). Its proof is exactly `by sorry`,
with the source and complete mathematical argument in its docstring and node.
Thus this is a decomposition: one original hole closed, one lower algebraic hole
added, and the entire exact target-coordinate argument proved. It is not an
axiom-free closure of the original theorem's dependency tree.

The algebraic lemma is true for zero complexes and identity localizations, and
there is no prime when the fourth ring is zero. The generic coordinate lemma
uses only module localization and exact functors, for arbitrary complexes and
module maps into their cohomology; it assumes neither K-flatness nor a cartesian
square. The pure nested tensors in the algebraic lemma generate each degree
as a module over the fourth stalk, so its normalization condition determines
the chain map.

## No longer needed

No existing imports were removed; both original public imports remain necessary
for the unchanged statement. Both new proof imports are used.

The original planned dependency `lem-pc-derived-tensor-localization-cohomology`
(module `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`) is not needed
by this route: the lower algebraic node uses the arbitrary-model first-factor
and base/second-factor localization results directly, rather than their
resolution-only composite. This is pruning of this item's planned route, not a
claim that the module is unreachable from all project targets.

All other original proof dependencies remain needed by the statement or by the
two new nodes. No additional pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or mathematical error was found. The original plan omits
executable interfaces for transporting the affine ring localizations and the
supplied global model (with its arbitrary derived-category universe) to the fixed
stalk model. This remains in the algebraic node; it is not supplied by merely
applying the resolution-only `derivedTensor_localization_cohomology` signature.
The exact tilde/stalk homology target transport was likewise not supplied by one
existing theorem, but is now fully proved using Mathlib's localization and exact
homology APIs.

The first compile temporarily lacked the newly landed
`AffineOrdinaryTensorStalkCoordinates.olean`; the normal shared-cache refresh
resolved that, with no dependency copied into the sandbox. LeanSearch returned
Internal Server Error; this is recorded as unavailable, with no mathematical
absence verdict inferred. LeanFinder, Loogle, and source searches were used.
The Stacks sources were read at Tags 0DJ8, 01I9 and 01AG on the official website.

## New nodes

`lem-pc-affine-stalk-scalar-extension-coordinates` records the proved generic
exact affine stalk scalar-extension coordinates, including numerator normalization
and the naturality square for arbitrary module maps into ordinary cohomology.
Its module is `Sheaf.Algebra.Homology.AffineStalkScalarExtensionCoordinates`.

`lem-pc-affine-scalar-localized-tensor-square` records the remaining algebraic
derived tensor model-localization square in scalar-extension coordinates,
before exact tilde/stalk homology transport. Its module is
`Sheaf.Algebra.Homology.AffineScalarLocalizedTensorSquare`.

There are no change records or forced adaptations.

## Second reading by S4

1. Diffed the delivered target module against the repository version. The theorem
   signature, definitions, and public imports required by the interface are unchanged;
   verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no compiler
   errors, forbidden declarations, or unlisted `sorry`s; the sole remaining `sorry` is
   the named algebraic split theorem and its node and docstring agree; verdict: pass.
3. Checked the two added statements against their hypotheses and edge cases (zero
   complexes and identity localizations), and searched the existing Lean declarations
   and Mathlib interfaces for duplicates. The statements are strictly intermediate
   reductions and are needed by the target proof; verdict: pass.
4. Traced the proof from the target downward. The scalar-extension coordinate theorem
   is proved, while the remaining algebraic model transport is explicitly split off.
   Proof-only imports were reduced to plain imports where applicable; verdict: pass.
5. Compared the DAG nodes with the Lean declarations and proof calls. The target node's
   route, dependencies, and unit are consistent, and the unit route is unchanged;
   verdict: pass.

Changed the two proof-only imports in `AffineStalkScalarExtensionCoordinates` from
`public import` to `import`, then recompiled the sandbox. No statements or definitions
were changed.
