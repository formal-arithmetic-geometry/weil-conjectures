## What changed

Proved `WeilConjectures.CompletedCoefficientPushforward.directImage_preservesComplete`
without changing its statement, definitions, or public imports. The proof uses the
principal uniformizer cone tower on the original independently sized sites instead
of transporting the full adic coefficient datum to small equivalent sites.

Private proved helpers extract the datum-independent part of the existing Roos/local
completeness argument, establish K-injectivity of the principal completion, and
construct the natural cone/product comparison for additive product-preserving
functors. Product preservation is proved sectionwise, using evaluation and scalar
restriction; this avoids the automatic adjoint instance that requires equal site
object and hom universes. The finite projection equations identify the image
scalar with the actual target uniformizer. The supplied `RightImage.computes` then identifies the result
with the requested derived image. Updated the declaration's proof docstring and
its node's `proof`, `proof_deps`, and `proof_origin` to follow this argument.

Validation: the final module passed `lcompile.py` without warnings (17.9 seconds).
A subsequent sandbox compilation checked the item (20.8 seconds) and the original
`Sheaf.Paper.CompletedCoefficientPushforwardComparison` against it (14.1 seconds),
both successfully without warnings. The temporary unchanged consumer copy was
removed after this check and is not part of the delivery. The declaration text
and public imports are byte-identical to the original; all Lean lines meet the
100-character bound.

The static interface checker flags the new helper-section commands. The required
record is `coord/changes/K1-completed-direct-image-private-helpers.md`; it records
the identical old/new public signature and the unchanged comparison consumer.
No mathematical interface or target statement changes.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.CompletedCoefficientPushforward.directImage_preservesComplete`
(node `lem-pur-completed-direct-image-preserves-completeness`). Added zero holes;
zero holes remain in the delivered module. Every private helper is proved.
Existing imported statements, in particular the principal local criterion, remain
the project's separately assigned obligations; this delivery does not rename or
split the assigned hole.

## No longer needed

Removed exploratory direct proof imports of
`Sheaf.Algebra.Homology.KInjectiveProductsTermwise`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`. The K-injective product proof
uses the homotopy-category product lemma directly; the adjoint instance is not
used; the other required declarations are already publicly available through
the retained imports.

The following original direct proof dependencies are unnecessary for this node's
argument and are removed from its `proof_deps` and proof steps:

- `def-pc-perfect-ring-complex` (`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`);
- `def-weil-pbc-adic-coefficient-datum` (`Sheaf.Paper.AdicCoefficientDatum` and
  `Sheaf.Paper.AdicCoefficientDatumCompleted`);
- `lem-sfb-integers-profinite-tower` (`Sheaf.NumberTheory.Padics.IntegersProfiniteTower`);
- `lem-weil-l-adic-extension-integers-dvr` (`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`);
- `lem-weil-pbc-constant-completion-equivalence` (`Sheaf.Paper.ConstantCompletionEquivalence`);
- `lem-weil-pbc-profinite-coefficient-inverse-image`
  (`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`);
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
  (`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`);
- `lem-weil-valued-dvr-finite-quotients` (no Lean attachment);
- `prop-weil-pbc-direct-image-limits` (`Sheaf.Paper.CompletedDirectImageLimits`).

These dependencies were never imported by the original item. They are pruned from
this node's direct route; this does not assert that their modules are globally
unused. In particular, the existing Roos module still publicly imports the adic
datum interface. No source-library declarations or modules are removed.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically sound but unnecessarily packages a full adic
coefficient datum and coefficient/site equivalences. The existing Roos equivalence
also accepts such a datum although its local/principal argument never uses it.
Extracting that argument into a proved private helper permits the present theorem's
independent scheme and coefficient universes throughout. The old dependency
`lem-weil-valued-dvr-finite-quotients` also has no Lean attachment; this route does
not need it. No statement repair or forced adaptation is needed. The static command-layout
change is documented in the change record above. No new nodes or split-off obligations are introduced.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
