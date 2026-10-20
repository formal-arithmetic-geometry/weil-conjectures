## What changed

Implemented `WeilConjectures.finiteCompactProEtale` with its original signature and public imports. The proof constructs the essential-image localizing argument and explicitly transfers the canonical Hom direct-sum map through the fully faithful comparison. Private proved helpers handle coproduct comparison, componentwise injectivity and shrinking arbitrary existing coproducts to the Hom universe.

Added `AlgebraicGeometry.ProEtale.finiteDiscreteCtfOrigin`, a proved finite-Tor comparison antecedent result in the internal/fixed-scalar coefficient presentations. Its coefficient-reflection sub-result is isolated as `AlgebraicGeometry.ProEtale.finiteDiscreteCtfRealization`, the only remaining mathematical obligation; the main theorem does not assert compactness through that lemma by renaming its own conclusion.

The final delivery was rebased after `Sheaf.CategoryTheory.Triangulated.LocalizingFunctor` was pruned from the shared repository. The proof now applies the defining localizing-closure intersection directly; a proved private cofan lemma transfers small coproduct closure to every larger existing coproduct by omitting zero summands and shrinking the nonzero index subtype. Thus nodes `det-proper-image-localizing-principle` and `det-def-localizing-closure-existence` are no longer used; the statement already supplies its ambient coproduct.

The original sandbox contained the main proof and this lemma but no node or report. Retained that work, checked current source interfaces, removed an unused helper and locally suppressed the syntactic unused-instance-name warning (retaining the original binder), and supplied the DAG records. No existing statement, definition or public import changed. No consumer adaptation or change record is required.

## Proved and sorry left

Closed the original hole in `WeilConjectures.finiteCompactProEtale` (node `det-ctf-finite-compact-proetale`). Its full assembly proof compiles. Added one hole in the new public theorem `AlgebraicGeometry.ProEtale.finiteDiscreteCtfRealization` (node `lem-finite-discrete-ctf-realization`). The public theorem `AlgebraicGeometry.ProEtale.finiteDiscreteCtfOrigin` is proved from that strictly smaller coefficient-reflection statement. There are zero holes in the item module and one in the new realization module. This is a decomposition: one original hole closed, one separate comparison hole added, net zero; it is not a claim of a sorry-free compactness theorem. Every private helper is proved.

The remaining lemma is the source's coefficient-identification assertion, expressed for the specified realization: it reflects fixed-scalar bounded constructibility and finite Tor amplitude. The etale antecedent assertion itself is now proved. Its docstring and node give the proof, including all coefficient identifications. It is strictly part of the argument and says nothing about compactness or localizing families.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`
- `Sheaf.Paper.LocalizingClosureExistence`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`
- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.Paper.FiniteDiscreteSchemeRing`
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.ConstructibleSheaf.Refinement`

The direct `finiteComparisonLocalizing` equivalence/operations theorem is not used: the proof constructs the essential-image argument from full faithfulness and sum preservation. Its owning module remains needed for the specified coefficient realization and exactness. No entire module is withdrawn. Removed the now unused top-level tool approvals `lem-weil-pbc-finite-discrete-scheme-ring-constant`, `det-pe-finite-tor-comparison-noetherian`, and `lem-weil-pbc-constructible-qcqs-affine-local`; the first still occurs transitively through the specified realization definition. The antecedent proof instead uses the proved `fixedDerivedOrigin` helper in `Sheaf.Paper.ProEtaleConstructibleOrigin` (imported with `import all`) and the source-library `torAmplitudeIn_of_mapDerivedCategory` theorem in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison`. Thus `det-pe-finite-tor-comparison-noetherian` and the direct constructibility-convention bridge nodes are not needed as direct proof dependencies of this item or the origin lemma. Their modules may still occur through existing transitive imports; no claim of global module removal is made. The affine-component argument is replaced by Mathlib's finite-type/local-Noetherian instances. The source unit's route remains etale compactness, constructible finite-Tor site comparison, then unbounded comparison; the ordinary finite-Tor comparison is assembled from the existing bounded-origin and Tor-reflection lemmas.

## Where the brief, the DAG or earlier work was wrong

The stated finite-Tor comparison theorem uses intrinsic constant-ring modules on coefficient-sized sites; the item uses internal modules and fixed-scalar ordinary etale modules. Its current declaration is not a directly applicable antecedent lemma for the specified `finiteComparisonRealization`. The separate coefficient-presentation comparison remains necessary. The existing `moduleObject_ordinary_coefficient_equivalence` is normalized to a different fixed-scalar functor and ties the coefficient carrier universe to the scheme universe, whereas this item has `A : Type` and arbitrary scheme universe. Applying it directly produces a universe mismatch; it does not identify its functor with the specified `finiteComparisonRealization`. This functor-identification and its constructibility/tensor compatibility form the source-backed separate result left here, rather than a restatement of compactness.

Earlier compile attempts returned the 60-second timeout on a sorry-only statement; subsequent unchanged/near-unchanged compiles completed in seconds. No limit was raised and no file was split for compile speed. The final localizing argument uses generic private helpers in the same module; explicit local instances for the derived realization and composite functors avoid repeated instance expansion. The final standalone item compile completed cleanly in 30.8 seconds. The sandbox budget start changed between resumed attempts (from 1792425806.1569953 to 1792438008.8674955); the worker did not edit budget metadata or delay for the split policy. The existing report/node omissions were repaired.

## New nodes

`lem-finite-discrete-ctf-origin`: the proved finite discrete internal-to-etale constructible finite-Tor antecedent theorem, sourced from the finite-Tor comparison equivalence and the compactness source's first paragraph.

`lem-finite-discrete-ctf-realization`: the remaining coefficient-realization reflection theorem. It is a strict sub-result about preservation/reflection of bounded constructibility and finite Tor amplitude, with no etale antecedent or compactness conclusion. Tested edge cases: empty X, zero A and zero K are covered by the statement and proof plan. No new data-bearing definition and no noncanonical existence witness is used to define data.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
