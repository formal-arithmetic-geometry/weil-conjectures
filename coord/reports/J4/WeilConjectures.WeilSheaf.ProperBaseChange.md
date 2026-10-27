## What changed

Filled the sole hole in `WeilConjectures.WeilSheaf.ProperBaseChange` using the existing
`AlgebraicGeometry.nativeWeil_proper_natural_baseChange` declaration. The proof derives local
Noetherianity of Y and Y′ from their given structure maps, obtains quasi-separatedness by the
existing instances, supplies the chosen Cartesian square using `IsPullback.isoPullback`, evaluates
the natural isomorphism at K, and lifts that component with `ObjectProperty.isoMk`.

Added only private proof imports `Mathlib.AlgebraicGeometry.Noetherian` and
`Sheaf.WeilSheaf.NativeProperNaturalBaseChange`. All existing declaration signatures, definitions,
attributes, docstrings, and public imports are preserved. Updated the item's DAG proof to agree
with the Lean proof. No other existing module or node is changed.

Searches before writing: LeanFinder for proper base change of derived Weil complexes returned
ordinary pullback/pushforward comparison APIs, not this theorem; Loogle for `"IsPullback",
"IsProper"` returned no hits; the launcher's grep query for the two relevant declaration names
returned no hits. Direct `rg` over the source library and Sheaf found the existing
`NativeProperNaturalBaseChange` declaration, which is used.

## Proved and sorry left

Closed: `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`
(node `lem-weil-pbc-weil-complex-proper-base-change`): 1 of 1 original holes.

Added holes: 0. Remaining holes in the item: 0. No split-off statements or modules.
Validation: the final file compiled cleanly through `lcompile.py` in 4.5 seconds, exit code 0,
with no warnings. The compiler resolved the existing natural-comparison dependency in its
private overlay. All lines in the delivered Lean file are at most 100 characters.
The proof uses the existing theorem `AlgebraicGeometry.nativeWeil_proper_natural_baseChange`,
whose own proof currently contains `sorry`; this delivery closes the upper hole from that stated
dependency and does not claim that the entire transitive proof is axiom-free.

## No longer needed

No existing import is removed, and no module or declaration is withdrawn. Both added proof
imports are used. The following old direct proof dependencies are unnecessary at this node:

- `lem-sf-fixed-pair-created-abelian-structure`
  (`Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure`): the ambient natural comparison
  already lives in the native derived Weil category.
- `lem-sf-native-adic-constructible-pullback` and
  `lem-sf-native-adic-pullback-exact-lisse`
  (`WeilConjectures.SixFunctors.ProEtale.Adic.Constructible` and its public dependencies):
  the already-defined restricted `WeilComplex.upperStar` includes its preservation proof.
- `lem-weil-pbc-exact-functor-complex-cohomology`
  (Mathlib's `CategoryTheory.Functor.homologyFunctorIso` API): no new cohomology comparison is
  needed to restrict an isomorphism between objects already in the full subcategory.
- `lem-sf-native-weil-proper-shriek-star`
  (`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`): the already-defined
  `WeilComplex.derivedLowerStar` includes its preservation proof, so proper coincidence is
  unnecessary here.
- `lem-sfb-finite-type-composition-base-change` (Mathlib finite-type and quasi-compactness
  composition/base-change APIs): no new source finite-type instance is needed by the applied
  natural comparison.
- `lem-weil-pbc-proper-base-change` (Mathlib proper base-change API): properness of f′ is not
  required by the applied declaration, and its qcqs and local finite-type hypotheses are already
  present in the item's signature.

These are removed only from this node's direct proof dependency list. They may remain needed by
other nodes or by the existing operations and natural comparison; no claim of global pruning is
made. The blueprint unit's realized statements and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The old plan redundantly reproved preservation of bounded constructible objects and invoked
proper shriek-star coincidence for this purpose. The current native restricted operations already
carry that preservation, so the ambient component lifts directly. No statement correction or
change to a shared definition is required. The return file contains only the historical upstream
sync notice and no item-specific repair request; there is no rework/quarantine row for this item.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
