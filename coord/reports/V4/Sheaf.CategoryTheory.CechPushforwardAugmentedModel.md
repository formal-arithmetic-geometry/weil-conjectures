## What changed

Implemented the canonical strict and derived column constructions, normalized total
augmentation, module and cover naturality, and resolution transition laws in
`Sheaf.CategoryTheory.CechPushforwardAugmentedModel`.
The construction uses `CechInjectiveImageAugmentation` directly for the given
ringed morphism. Its existing complete proof needs no invertibility of the
structural ring map; the unused assumption was removed from its theorem only.
The column functor now evaluates the Cech degree before mapping the complex;
its maps and differentials are definitionally the same. The original existential
model predicate is retained. Private `import all` imports reuse the existing
column-model and normalized-naturality implementation helpers without changing
their modules or visibility. Mathlib `Functor.copyObj` and `Functor.isoCopyObj`
replace the local transport constructions. The assigned theorem and target
signatures are unchanged. The augmentation statement repair and consumer audit
are recorded in `coord/changes/cech-injective-image-general-ring-map.md`.

Repair of returned delivery `724afe8f731`: the independent reviewer passed the
mathematics, but its correction of the column change record was handed to
`--apply-fixes` with the delivery filename rather than the required
`cech-pushforward-column-representation.change.md` correction filename. The
record now documents this distinction and the public instance parameters. The
retained Lean work and both node copies have been compared with current
`sheaf-dag`; the augmentation adaptation is still exactly the removal of the
unused ring-map invertibility instance. The delivery tool rebases the complete
packet on its freshly fetched `sheaf-dag` before committing it.

## Proved and sorry left

The proof closes the sole original hole in
`CategoryTheory.CechPushforward.cech_pushforward_augmented_model`, from the
existing column-model and normalized-naturality declarations and the proved
image-augmentation theorem. The assigned module now contains zero holes.
Added holes: zero. Split-off statements: zero. The adapted
`CategoryTheory.CechInjectiveImage.cech_injective_image_augmentation` remains
proved with zero holes before and after removing its unused assumption.
All newly added private helpers are proved or explicitly constructed. No new nodes or split-off results were introduced.

The original two-module packet compiled and passed preflight before delivery.
The returned landing has no compiler-error file for this module. On repair, an
initial fresh compile timed out; the server-only two-module check then passed
with exit code 0 and no warnings. Temporary profiling options were removed.
The delivery tool reruns compilation, preflight and its axiom probe on the final
packet. The assigned theorem signature matches current `sheaf-dag` verbatim.


## No longer needed

The separate `lem-sfb-injective-finite-total-derived-comparison`
(`Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison`) is not used:
sectionwise exactness gives the actual pushed augmentation directly.
The explicit module adjunction is already a hypothesis, so the proof does not
use `lem-weil-pbc-ringed-topoi-module-adjunction`; its obsolete top-level tool-use
entry is removed. Slice resolutions use the general RingCat small-site theorem
`lem-weil-pbc-ring-sheaves-grothendieck` rather than the CommRingCat generator
theorem `lem-pur-ringed-site-grothendieck-abelian`.
Removed imports: `Sheaf.CategoryTheory.SiteCoveringAxioms` (already publicly provided by the column
interface), `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
(the existing ordinary right-derived functor is used),
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` (the needed adjunction
is a hypothesis), `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
(the general RingCat theorem applies), and the explicit imports of
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves` and
`WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
(their required APIs are already supplied by the retained public imports).
The proof uses the canonical generic composition primitive underlying the
normalization theorem and proves its stronger all-complex unit equation directly;
the normalization node remains a statement dependency explaining its canonical
interpretation, while the proof cites the already proved generic composition
and exact-adjoint K-injectivity nodes.


Removed the unused public import of `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`; the proof uses its generic source comparison directly. Its needed public typeclass and functor interfaces are imported from their defining modules. There are no current Lean importers of the assigned item; all unfinished DAG parents are retained.

## Where the brief, the DAG or earlier work was wrong

The planned identity-only use of exact image augmentation was unnecessarily
restrictive: the existing section-comparison, injective-presheaf acyclicity,
effective-epimorphism descent, and first-quadrant total proof are already valid
for an arbitrary structural ring map. Removing the unused `IsIso f.ringMap`
assumption preserves the proof and avoids the separate finite-total derived
comparison. Both DAG citers still hold; their uses are audited in the statement
change record. The unit route and the assigned theorem signature are preserved.

The column representation repair is recorded in
`coord/changes/cech-pushforward-column-representation.md`. Its consumer audit
includes all three unfinished DAG parents. The original model witnesses and
normalization equations are retained.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
