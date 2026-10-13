## What changed
Closed `AlgebraicGeometry.nestedOpen_single_directImage_comparison` without changing its
signature, visibility or docstring. The proof composes ordinary restrictions, cancels the
open-site equivalence, derives the cartesian comparison through the existing generic
right-derived-functor APIs, and identifies restriction with tensor pullback by uniqueness
of left adjoints. Independent derived-category universes are preserved.

The cartesian comparison reuses the existing proved private
`AlgebraicGeometry.Scheme.Modules.pushforward_restrict_square` from
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` through a proof-only
`import all`. All added imports in the item are proof-only.

Added `Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`, proving
finite-limit and K-injective preservation for arbitrary open immersions by factoring
through the image open and transporting the existing open-subset theorem through
an equivalence. Its sectionwise additivity instance is also proved. Public imports of
this new module supply its signatures; all other imports are proof-only.

## Proved and sorry left
Closed one original hole:
`AlgebraicGeometry.nestedOpen_single_directImage_comparison`
(node `lem-pc-nested-open-single-direct-image-comparison`).

Also proved `AlgebraicGeometry.openImmersion_restriction_derived_properties` and
`AlgebraicGeometry.restriction_additive`
(node `lem-pc-open-immersion-restriction-derived-properties`).

Zero holes added; zero `sorry`s remain in delivered modules. This is a proof, not a
hole decomposition. The local compile and delivery axiom probe check all delivered
declarations; the scratch `#print axioms` check reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed
No original import was removed: all three public imports serve the unchanged signature.
The old proof dependency `lem-pc-restrict-derived-direct-image-open`
(`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`) is no longer used by this
item. It was not imported in the original file. The proof instead uses the existing
underived comparison and generic derived-functor composition. This prunes this item's
DAG edge; it does not claim that other consumers of that module disappear.

The second reading removed the duplicate proposed module
`Sheaf.AlgebraicGeometry.OpenImmersionModuleDirectImageComparison` and its proposed node
`lem-pc-open-immersion-module-direct-image-comparison` before delivery. The remaining
helper needs no import of `DerivedOpenRestrictionMaps`.

## Where the brief, the DAG or earlier work was wrong
The original derived comparison for `f ∣_ U` did not directly match the cartesian
pullback of the composite open immersion. Deriving the ordinary cartesian comparison
avoids an additional transport lemma. The first worker overlooked the exact private
underived comparison already in `DirectImage.Sections`; the second reader reuses it.

## New nodes
`lem-pc-open-immersion-restriction-derived-properties` records the fully proved extension
of the open-subset K-injective theorem to arbitrary open immersions, together with
finite-limit preservation supplied by the existing library instance. Its chapter,
unit and blueprint ancestry agree with the item. No change record is needed because
no existing interface changes.

## Second reading by U3
1. Compared the item with the repository version: its existing signature and docstring
   are byte-for-byte unchanged. No existing definition or visibility changes. The new
   helper's statements express finite-limit and K-injective preservation and additivity.
2. Read the proofs and compiled the delivered files locally. No `sorry`, forbidden
   declaration, or hollow definition occurs. A scratch copy's `#print axioms` checked
   the main theorem and helperdeclarations; only the three permitted axioms occur.
3. There are no split-off holes. The helper is valid for empty opens, identity
   immersions, empty schemes and zero complexes: equivalences and restriction require
   no nonemptiness. Independent LeanFinder and Loogle searches plus local `rg` located
   the exact existing private cartesian comparison, which replaces the duplicate.
4. The main proof performs the required ordinary comparison, K-injective restriction,
   and derived transport. The unit `sk-thm-picard-coherence` has no realized node
   referencing this item or the removed dependency; no realized unit step is bypassed.
   All old unused proof dependencies are listed above. Imports were checked against
   their use in signatures and proofs.
5. Read the item and new node records against the Lean code. Their proof steps,
   proof dependencies and origin describe the actual argument; the new node has the
   required source, search, creation, blueprint and Lean fields.

Changed on second reading: removed the duplicate cartesian-comparison module and node,
reused the existing private proof by `import all`, updated the item's DAG route, and
replaced a proof-only public import in the remaining helper with its narrower signature
import, then removed the now-unnecessary proof import and updated that node's route.

Removed the local abbreviation for the composite immersion in the proof to avoid a
kernel auxiliary-declaration type mismatch exposed by the proof-only `import all`.
