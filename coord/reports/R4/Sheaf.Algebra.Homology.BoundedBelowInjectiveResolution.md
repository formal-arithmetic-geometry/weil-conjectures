## What changed

Proved `SheafOfModules.exists_boundedBelow_injective_resolution` in
`Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`, without changing its signature.
Use the proved upstream sheaf-module Grothendieck theorem, Mathlib's enough-injectives
instance, the unbundled bounded-below injective replacement, and Mathlib's K-injectivity theorem.
The replacement has the same lower bound as the input. All existing public imports stay unchanged;
the replacement proof imports are private. Updated the item's proof docstring and DAG proof route.

## Proved and sorry left

Closed: `SheafOfModules.exists_boundedBelow_injective_resolution`
(node `lem-sc-bounded-below-injective-resolution`). One of one original holes is proved.
No sorries remain in the item, and no holes or new declarations were added.
The upstream Grothendieck theorem used here is already proved; the other results are Mathlib.
The single-file compile passed with no errors or warnings.

## No longer needed

Removed proof import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`, representing
`prop-pur-kinjective-resolutions-exist`. Its general unbounded, functorial resolution is unnecessary:
only the Grothendieck property is needed. Its assertion in
`lem-pur-ringed-site-grothendieck-abelian` is supplied directly by the proved upstream
`SheafOfModules.isGrothendieckAbelian`. The second reading additionally removes the proposed
proof import `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`, avoiding its
localized-generator construction. The Grothendieck assertion of that node remains a logical
dependency, but its stronger generator assertion and its Sheaf module are not used.
Consequently this item's route no longer needs the general-resolution proof branch
`lem-pur-kinjective-degreewise-existence` or its source module
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`, imported by
the removed module. These may still be needed by other consumers; no global unreachability is claimed.
The bounded-below replacement node and both Mathlib leaves remain needed. Using the unbundled
Mathlib construction avoids an import of
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives` and all glue for
forgetting the `InjectiveObject` packaging; its underlying replacement theorem is still used.
The unit `sk-thm-picard-duality` has empty realized statement and step lists, and no unit route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof route imported a theorem giving general functorial K-injective resolutions
merely to obtain its Grothendieck-property conjunct. The proved upstream Grothendieck-only theorem suffices.
Mathlib's unbundled replacement has precisely the requested existential shape; the originally
named bundled theorem adds unnecessary conversion work. No mathematical statement is disputed.
The repository has no `literature/stacks-project/*.tex` files, so the actual proof was checked
against the complete local Mathlib proofs and the proved ringed-site module instead.

## Second reading by R4

1. PASS: Compared the sole delivered module with the repository by diff. The existing
   theorem signature is byte for byte unchanged. No definitions, declaration visibility,
   public imports, hypotheses or conclusions changed; no change record is needed.
2. PASS: Compiled the submitted proof and the final repaired module with lcompile.py.
   A scratch copy with `#print axioms SheafOfModules.exists_boundedBelow_injective_resolution`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   No forbidden declarations, hidden holes, or definitions choosing unproved witnesses exist.
3. PASS: No statements were split off and no new declarations or nodes were added.
   Read the replacement theorem and its truncation proof in Mathlib CM5a, the bounded-below
   K-injectivity proof, and the upstream Grothendieck theorem. Their hypotheses match the
   small equal-universe site and underlying ring sheaf. The construction works for any
   integer lower bound, including negative bounds and the zero complex; no nonzero or
   positive-bound assumption is introduced. Existential elimination occurs only in a proof.
4. PASS after simplification: The first worker already uses the direct unbundled Mathlib
   replacement. Source search found an additional shorter route for its first step:
   `SheafOfModules.isGrothendieckAbelian` gives the required property directly, without
   constructing the localized generator. Replaced that proof import and instance source.
   Remaining private imports provide the replacement, enough injectives, and the upstream
   Grothendieck theorem. Existing public imports stay as the reviewed interface.
   `No longer needed` lists the sole removed old proof dependency and the additionally
   avoided generator module. Read the unit record: its realized statement and step lists
   are empty, and this tool-level replacement does not change the unit or chapter route.
5. PASS after metadata update: The node's proof steps, dependency union, and proof origin
   describe the actual upstream Grothendieck assertion, Mathlib replacement, and K-injectivity
   proof. The same Grothendieck node records the assertion used, explicitly excluding its
   additional generator clause. The replacement leaf is realized by the underlying
   unbundled theorem used in its recorded bundled Mathlib theorem. No new nodes need fields.

Changed during second reading: replaced the localized-generator theorem's first conjunct
with the proved upstream Grothendieck theorem; updated its private import, proof docstring,
node proof/origin, and pruning report. The resolution and K-injectivity argument is retained.
Closed one original hole and added zero holes: this is a proof, not a decomposition.
