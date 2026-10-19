## What changed

Proved `AlgebraicGeometry.ProEtale.exists_proEtale_closedSupportTriangle` without changing
its signature or the public declarations. All new helpers are private and proved. The six helper class proofs are private theorems
registered as local instances in the proof section; no global instance is added.
The explicit scalar-restriction functor is inverse to the recorded coefficient realization,
including for noncommutative finite rings. Its sectionwise pushforward comparison and the
adjunction-induced pullback comparison transfer the existing geometric facts. A homology/cone
argument proves the needed derived essential-image assertion. The existing proved formal
recollement API constructs the exceptional adjoint and the distinguished triangle with the
actual adjunction counit and unit. The two localization isomorphisms are canonical termwise
derived-functor factorizations. The retained duplicate core draft was removed from the sandbox;
it was never a library module. No other library module is changed.

Added proof imports: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion`,
`WeilConjectures.CategoryTheory.Triangulated.Recollement`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`, and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`. The existing Grothendieck
module-sheaf import is retained.

The original theorem docstring describes the longer K-injective/kernel proof plan. The node's
proof now records the shorter argument actually checked in Lean. The blueprint unit record
`sk-prop-sf-localization` has empty realized statement and step lists; its route is preserved.

Validation: on 2026-10-19 the required resumed dry run compiled the retained module and
passed delivery preflight (dry-run commit `1766f71867`, review class CODEX). Source comparison
confirmed both existing public signatures and all public imports unchanged; there are zero
`sorry` tokens and every Lean line is at most 100 characters. The scope-command change record is
`coord/changes/T9-proEtaleClosedSupportTriangle-local-helpers.md` and lists the 119 downstream
importers from the completed downstream check.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.ProEtale.exists_proEtale_closedSupportTriangle`
(node `lem-exc-proetale-support-triangle`). Original holes: 1. Remaining holes in this module: 0.
Holes added: 0. No split-offs. All private comparison and recollement helpers have complete
proofs. Imported declarations may still depend on existing project sorries, as allowed in stage 3.
The existing proved zero-map instance is unchanged.

## No longer needed

The proof avoids degreewise-injective resolutions, free-Yoneda sheaves, the injective open-unit
epimorphism, scalar reduction to Z/n, and supported-kernel-complex assembly. It instead uses
the source library's exactness, closed full faithfulness, disjoint vanishing and joint detection,
followed by its proved formal recollement API.

Removed proof imports:

- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage`
- `Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex`
- `Sheaf.CategoryTheory.RingedSiteModules`

Obsolete top-level tool approvals removed from the node:

- `lem-pur-kinjective-degreewise-existence`
- `lem-pur-kinjective-restrict-localized`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-free-yoneda-presheaf-module`
- `lem-weil-pbc-ringed-site-module-sheafification-exact`
- `lem-weil-pbc-cochain-complexes-degreewise-exact`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`

Original proof-dependency nodes not used directly by this route:

- `def-sp-injective-resolutions`
- `def-weil-pbc-proetale-site`
- `def-weil-sheaf-of-modules-category`
- `det-sf-open-closed-sequence-ring-sheaf`
- `lem-exc-proetale-closed-essential-image`
- `lem-exc-proetale-derived-adjunction-triangle`
- `lem-exc-proetale-open-derived-image`
- `lem-exc-proetale-supported-kernel-complex`
- `lem-pur-kinjective-degreewise-existence`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-weil-pbc-free-yoneda-presheaf-module`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-weil-pbc-ringed-site-module-sheafification-exact`
- `lem-weil-proetale-weakly-etale-localization`

These are direct dependency prunings, not assertions that their modules are absent from every
transitive import or every other target. Existing public imports are retained to preserve the
module's public interface. The existing source-library formal recollement declarations are
proved generic tools; no new geometric or categorical statement is assumed. The source
closed-exactness and closed-full-faithfulness nodes are used as tools with exactly their
recorded finite-ring statements; the additional disjointness and joint-zero-detection
lemmas are proved in that same source-library API. No new tool approval is inserted.

## Where the brief, the DAG or earlier work was wrong

The retained earlier draft moved the whole conclusion into
`exists_proEtale_closedSupportTriangle_core`; that was not a valid decomposition and is not
part of this delivery. The current finite-module sources expose
`finiteCoefficientRealization_isEquivalence_ring`, so no commutativity assumption or arbitrary
coefficient equivalence is needed. The kernel-complex plan is valid but substantially longer
than the existing formal recollement route. No statement is disputed or altered.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
