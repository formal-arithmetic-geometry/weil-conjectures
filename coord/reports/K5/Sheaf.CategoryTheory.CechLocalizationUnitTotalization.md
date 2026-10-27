## What changed

Replaced the sole proof hole in
`CategoryTheory.CechLocalizationUnit.cech_localization_unit_totalization` by a complete
Lean assembly. It obtains a functorial augmented pushforward family and applies a generic
exact-unit comparison to that family. The source columns are transported by
`T_D RG(b.columnIso)`, and the target columns by `T_D RG(H_D(b.columnIso))`.
The proved private lemma `map_square_then` transports all four operator/refinement
squares. Functoriality transports both augmentation equations. Naturality of the actual
`exactUnit hAdj.unit` at each column isomorphism gives `unit_columns`. The total square
comes from the generic family theorem. Applying `congrArg` of the specified derived slice
restriction gives the final restriction assertion.

Moved the original supporting declarations verbatim into the new
`Sheaf.CategoryTheory.CechLocalizationUnitModels`, publicly imported by the assigned
module. Added the `PushforwardFamily` and `UnitFamily` interfaces there. The extraction
avoids cycles between the assigned theorem and its two new proof lemmas. No definition
contains a hole, arbitrary existence-based choice or changed old data. The original
theorem signature and the complete text of every extracted declaration were compared
and found identical. There are no direct Lean importers of the assigned module, so no
existing consumer needed adaptation.

The four modules compiled together through lcompile.py, in import order: models 33.2 s,
pushforward family 5.9 s, exact-unit family 4.6 s, assigned theorem 14.3 s. All are below
60 s; there were no errors or warnings. The proof removes the original
`backward.isDefEq.respectTransparency false` option. Lines are at most 100 characters.

Change record: `coord/changes/K5-cech-localization-model-extraction.md`.

## Proved and sorry left

Closed the existing hole in
`CategoryTheory.CechLocalizationUnit.cech_localization_unit_totalization`
(node `lem-sfb-cech-localization-unit-totalization`); zero holes remain in its module.
Also proved the private categorical transport helper `map_square_then`.

Added exactly two holes, both public named theorems with a complete proof in words:

- `CategoryTheory.CechLocalizationUnit.cech_pushforward_augmented_family`
  (`lem-sfb-cech-pushforward-augmented-family`): strict assembly over the arbitrary
  parameter category of the existing normalized pushforward model. This concerns only
  f, the cover and the input module; there is no H, G, T or unit-total square.
- `CategoryTheory.CechLocalizationUnit.exact_unit_augmented_family`
  (`lem-sfb-exact-unit-augmented-family`): the generic exact-unit derived comparison for
  an already supplied strict augmented family. There are no sites, covers, slice
  localization columns or Cech-model construction in its statement.

This is a decomposition of one upper hole into two distinct lower assembly tasks,
not a claim of a net mathematical proof. The original planned dependency theorems
`cech_pushforward_augmented_model` and `exact_unit_derived_total_square` are already
proved, but expose objectwise and compatible-lift equations rather than the exact
strict P-family interfaces needed here. The two new lemmas supply that missing assembly;
neither restates the assigned theorem, and the proof combining them performs the
canonical-column transport and actual-unit naturality explicitly.

## No longer needed

The following direct private imports of the original module are removed:

- `Sheaf.CategoryTheory.DerivedCechImageTotalization`.
- `Sheaf.CategoryTheory.NonnegativeDerivedTotalization` (still needed transitively by
  the generic family argument; no mathematical pruning of that node is claimed).
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`.
- `Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation`.

The old public dependencies are re-exported through CechLocalizationUnitModels rather
than repeated on the original module's header. The core uses the existing generic
K-injective-resolution instances instead of importing DerivedCechImageTotalization
just for its module-resolution instance.

A source import-closure comparison removes these project modules from this item's
closure (they may still be reached from other targets or other parents):

- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`.
- `Sheaf.CategoryTheory.DerivedCechImageTotalization`.
- `Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`.
- `Sheaf.CategoryTheory.IndexedCoveringClass`.
- `Sheaf.CategoryTheory.SheafSubcategoryComparison`.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`.
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`.
- `Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison`.
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`.
- `Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation`.
- `Sheaf.CategoryTheory.SmallSetOfCoveringFamilies`.
- `Sheaf.CategoryTheory.ToposCompatibleGenerators`.

Their attached nodes are no longer needed along this proof route:

- `def-trf-geometric-morphism` (`Sheaf.CategoryTheory.Sites.GeometricMorphism`).
- `def-weil-pbc-indexed-covering-class` (`Sheaf.CategoryTheory.IndexedCoveringClass`).
- `def-weil-pbc-topos` (`Sheaf.CategoryTheory.Sites.GrothendieckTopos`).
- `lem-sfb-derived-cech-image-totalization` (`Sheaf.CategoryTheory.DerivedCechImageTotalization`).
- `lem-sfb-derived-composition-adjunction-normalization` (`Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`).
- `lem-sp-derived-injective-resolution-naturality` (`Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`).
- `lem-trf-sieve-sheaf-subcategory-presentation` (`Sheaf.CategoryTheory.SheafSubcategoryComparison`).
- `lem-trf-topos-localization-site-presentation` (`Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation`).
- `lem-weil-pbc-localized-sheaves-over-representable` (`Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`).
- `lem-weil-pbc-over-post-continuous-general` (`Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`).
- `lem-weil-pbc-sheaf-subcategory-comparison` (`Sheaf.CategoryTheory.SheafSubcategoryComparison`).
- `lem-weil-pbc-slice-set-pullback-isIso` (`Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison`).
- `lem-weil-pbc-small-set-of-covering-families` (`Sheaf.CategoryTheory.SmallSetOfCoveringFamilies`).
- `lem-weil-pbc-topos-compatible-generators` (`Sheaf.CategoryTheory.ToposCompatibleGenerators`).

The original plan's two substantive dependencies remain needed through the new lemmas;
the exact slice restriction remains needed in the definitions. Removed obsolete
`tool_uses` entries for the now-unused direct composition-normalization and site-
presentation routes. No module is withdrawn or emptied, no DAG node is deleted, and
no upstream declaration or proof is changed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan correctly identifies the two mathematical inputs. Its Lean
interfaces do not directly furnish strict functors on an arbitrary P: the pushforward
model theorem supplies a model for each N,V and transition equations for compatible
resolution lifts, while the exact-unit theorem supplies compatible replacements and
naturality. Their strict simultaneous assembly needs its own Lean work. The two new
lemmas state precisely those separate tasks. Existing definitions and the target
statement were correct and are preserved.

The exact unit used in the column transport is the specified `hAdj.unit` descended
by `exactUnit`, rather than a unit on an isomorphic composite or a sliced adjunction.
No sliced h-adjunction is introduced. Edge cases checked: empty P gives the empty
strict families; N=0 and the terminal cover preserve the normalized augmentations;
identity H with identity eta gives the identity comparison; zero or noninvertible eta
is still admitted; negative degrees vanish by extension, and all total diagonals are
finite. Neither H nor T is assumed to preserve injectives. The abstract family proof
resolves H's image separately and uses a homotopy equivalence between bounded-below
injective point and total complexes before applying G.

## New nodes

`def-sfb-cech-localization-unit-models` records the extracted total, exact descent,
augmented models, canonical columns, comparison and restriction API, together with the
two new family structures. It is a definition node with no sorry or existence claim.

`lem-sfb-cech-pushforward-augmented-family` records the source-family assembly, from
`lem-sfb-cech-pushforward-augmented-model` and
`lem-sfb-cosimplicial-injective-total-replacement`. Its docstring and node give the
strict resolution-functor construction, canonical column equations and normalization.

`lem-sfb-exact-unit-augmented-family` records the independent abstract family assembly,
from `lem-sfb-exact-unit-derived-total-square` and
`lem-sfb-cosimplicial-injective-total-replacement`. Its docstring and node explain the
strict simultaneous replacements, point/column comparisons, augmentation quasi-
isomorphisms and localization uniqueness identifying thetaD with exactUnit.

Searches were run through msearch.py (LeanSearch, Loogle, LeanFinder and grep), with
actual results in searches.jsonl and in the new node records. Relevant existing
project interfaces were read in full. Blueprint ancestor/search commands give no
imported ancestor and no duplicate for augmented Cech/exact unit; the inherited
paragraph-(3) provenance is retained. Sources read locally: Stacks
sites-cohomology.tex, lemma-injective-module-trivial-cech (03FC); derived.tex,
lemma-functorial-injective-resolutions (0141), lemma-right-derived-exact-functor (015F),
and lemma-two-ss-complex-functor (015J); current blueprint latest direct-images proof
paragraph (3). No unit or chapter route is bypassed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
