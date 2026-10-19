## What changed

Retained and checked the interrupted sandbox against the current shared sources. Proved the
Hom and Isom composition laws using sheafification extensionality on binary products, the
comparison adjunction units, and pullback of actual localized derived maps.

Reduced the simultaneous bijectivity theorem to the canonical Hom-sheaf comparison for a
bounded finite locally constant source. The constant source is proved bounded with finite
locally constant cohomology using exactness, derived homology comparison, and constant
geometric stalks. Four Hom comparisons give the Isom comparison; both evaluation maps are
then composites of bijections. The new Isom comparison theorem is completely proved: its
inverse-pair presheaf is an equalizer, both functors preserve its products and equalizer,
and all canonical comparison squares are checked on actual maps through the adjunctions.

Reduced scalar evaluation compatibility to the coherent local construction of derived
extension of coefficients. The retained proof extends the actual-local-map square through
both adjunctions and then cancels the bijective pro-etale units, for Hom and Isom separately.
No definition or existing public signature changed. The three new modules are proof imports
of the item; the equalizer machinery is a proof import of the Isom module.

Validation: all four modules compile together through lcompile.py. After moving the
filtered-colimit instance into its proof and removing an unnecessary elaborator option,
the main module compiled in 44.8 seconds.
Existing public signatures and both existing
definition bodies are unchanged. The current C7 derived-presheaf proof-context, Q1
Over.post-continuity, and F7 finite-coefficient direct-image import change records were
checked; each preserves this consumer's interface and requires no adaptation. All Lean lines have at most 100 characters.

## Proved and sorry left

Original baseline: four holes. Item module now has zero holes.

Direct proofs closed:
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_composition`.
- `AlgebraicGeometry.Scheme.derivedMorphism_isoEvaluation_composition`.

Two original declarations are decomposed, rather than counted as independent proofs:
- `AlgebraicGeometry.Scheme.derivedMorphism_weaklyContractible_evaluation` is proved from
  the Hom-model comparison, the completely proved four-Hom-to-Isom theorem, and the existing
  weakly contractible unit-bijectivity theorem.
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_scalarExtension` is proved from
  the coherent local scalar-extension construction, with actual Lean proofs of the passage
  from local maps to both evaluation identities.

Additional theorem fully proved:
`AlgebraicGeometry.Scheme.derivedIsoSheafComparison_isIso_of_hom`, node
`lem-weil-pbc-derived-isom-comparison-from-hom`.

Exactly two holes are added, each a public theorem in its own new module:
- `AlgebraicGeometry.Scheme.derivedHomSheafComparison_isIso_lisse`, node
  `lem-weil-pbc-derived-hom-sheaf-comparison-lisse`. This is the finite-free RHom model
  and canonical-map comparison part of the original argument; it asserts no evaluation,
  Isom, composition or scalar-extension result.
- `AlgebraicGeometry.Scheme.derivedScalarExtension_localSystems`, node
  `lem-weil-pbc-derived-scalar-extension-local-systems`. This is the K-flat localized
  construction and its normalization on actual maps; it asserts no sheaf-section evaluation
  compatibility. It applies to arbitrary rings, including non-flat coefficient quotients.

Thus four original holes close and two lower holes are added: two direct proofs and two
substantial reductions, with net two fewer holes. Both remaining results have complete
source-based proofs in their docstrings and nodes. There is no sorry in a definition or
private declaration. All other original declarations are retained without holes.

## No longer needed

No modules are globally pruned. The original finite-free/RHom and K-flat routes remain needed
inside the two separate results, and the blueprint unit route is retained. They are not
claimed as discarded work.

Direct proof imports removed from the item (their remaining uses, where required, are
inside the separate Hom or scalar argument; none is claimed globally pruned):

- `Sheaf.RingTheory.RingPseudoCoherent`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`.
- `Sheaf.Algebra.Homology.HomComplex`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`.
- `Sheaf.Algebra.Homology.RhomGlobalSections`.
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.Algebra.Category.Ring.Limits`.
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`.
- `Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`.
- `Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`.
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
- `Mathlib.Algebra.Category.Grp.AB`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.CategoryTheory.DerivedMorphismPresheaf`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

The parent no longer cites the following proof dependencies directly: the pseudo-coherence
criterion, the pseudo-coherent complex definition, bounded-free RHom model, internal-Hom and
Hom-complex definitions, sheaf-Hom, global derived Hom formula, K-injective resolutions and
slice restriction, exact module sheafification, exact module restriction, exact comparison
inverse image, finite-ring derived local constancy, and canonical derived tensor pullback.
Those dependencies are recorded on the new Hom or scalar node at their actual use. The
weakly contractible evaluation input is supplied by the already stated
`proEtaleDerivedUnits_bijective` in the comparison interface. The parent does not reproduce
its proof. Constant-sheaf restriction and the size convention are likewise supplied by the
existing constant and comparison interfaces. No existing public import was removed because
its statement-level interface is preserved. An exploratory import of
`Mathlib.CategoryTheory.Limits.Types.Equalizers` was removed from the new Isom module.

## Where the brief, the DAG or earlier work was wrong

The retained report was stale: it did not describe the scalar reduction or its added hole.
The earlier scalar helper had no matching DAG node. Both are corrected here. Source labels
were checked against the local Stacks tag database: 094G belongs to Cohomology on Sites,
and the Isom node now cites sites.tex for 00WJ. The new helper's source labels were clarified: 06YY constructs derived pullback, 0D6D is composition, 07A4 is
tensor compatibility, and 0G7E preserves K-flat flat-term representatives. Preflight classified a file-level local filtered-colimit instance as an interface change.
It was moved into the constant-stalk proof as a local `have`, avoiding any new module-level
instance declaration or consumer adaptation. A subsequent preflight also identified a
module-level elaborator option as an interface command change. The option was unnecessary:
it was removed and all four modules compiled again. No mathematical statement discrepancy or
target-signature change was found. The search records on each new
node now retain only queries relevant to that node, including three kinds of search.

The resumed dispatch reset the local reference clock: the retained .budget now records
start 1792429584.374957 (2026-10-19 17:06:24 UTC), while searches and retained work date from
2026-10-19 00:36 UTC and earlier files. The earlier dry-run log recorded a different clock
(15 of 120 minutes). No budget metadata was edited. There were several provider interruptions;
compilation results were retrieved before repeating the affected operations. The retained
files did not identify the earlier provider attempt IDs. No prior push was found in the
retained delivery logs.

## New nodes

`lem-weil-pbc-derived-hom-sheaf-comparison-lisse` is the separate bounded-free RHom comparison
and identification of its canonical map (Stacks 08JI, 08JA and 094G). It remains a named hole.

`lem-weil-pbc-derived-isom-comparison-from-hom` is the finite-limit inverse-pair argument
(Stacks 00WJ). Its Lean proof is complete, with no new assumptions about boundedness.

`lem-weil-pbc-derived-scalar-extension-local-systems` is coherent localized K-flat scalar
extension with its three unit normalizations and actual-local-map square (Stacks 06YY, 0D6D,
07A4 and 0G7E). It remains a named hole. There are no change records because no existing
statement or definition was changed.

Further proof work checked the scalar construction in a separate scratch file: the ordinary
slice balancing isomorphism, its unit equation, the K-flat quasi-isomorphism preservation
argument, the derived adjunction, its identification with the existing fixed left adjoint,
and the derived-unit/counit factorization all compile. These partial constructions do not
prove slice invertibility and the full coherence statement, so they are not counted as
additional closed holes or added as unused delivery declarations. The scalar docstring and
node now specify the canonical adjunction mate and the derived unit factorization explicitly.
The local Stacks sources were reread at 08JI, 094G, 06YY and 0G7E to check their hypotheses.
For the Hom result, the existing bounded-free theorem uses a small site and SheafOfModules;
the native comparison uses the essentially small etale site and fixed-ring module sheaves.
Transporting the model and its canonical maps across these presentations is still needed.
For scalar extension over a Noetherian coefficient ring, the common class of complexes
that are K-flat both before and after slice restriction was also checked to be a left
derivability structure using the existing functorial flat resolutions. The subsequent
canonical comparison and its full coherence are still missing.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
