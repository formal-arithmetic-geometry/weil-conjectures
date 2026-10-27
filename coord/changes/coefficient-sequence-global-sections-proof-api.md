# Sheaf.CategoryTheory.CoefficientSequenceGlobalSections

## Reason

Fill the assigned theorem's proof with private helpers and private proof imports.
The generic derived-pair helpers use a scoped `Generic` section with fresh universe
variables; this adds commands outside the theorem proof. Irreducibility attributes on the private constructions prevent proof elaboration
from repeatedly unfolding their data.
This record covers those proof-interface commands. No existing signature, public
import, public attribute, definition body, or instance body changes. No target or
upstream source-library declaration changes.

## Old

Original imports, verbatim:

```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemDerivedTransition
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
```

Original universe prelude:

```lean
universe u v w a av b bv dA dD
```

The original theorem has its unchanged signature and `:= by sorry` proof.

## New

Imports:

```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemDerivedTransition
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Sheaf.CategoryTheory.TowerRightDerivedEvaluation
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.CategoryTheory.CoefficientRestrictionSectionsAcyclic
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
```

The universe prelude is unchanged. Before the concrete coefficient declarations,
proved private square-localization helpers use a scoped `GenericLocalizedSquare`
section with independent category and localization universes. Strict transparency
keeps their specialization from unfolding localization constructions. The proof reuses
the proved private exact-square factorization helper from `DerivedExactSquareComposition`. After
`SequenceSectionsDerivedPair`, a scoped
`section Generic` introduces `universe da db sep` and parameters `E`, `F` with their
category, abelian, and derived-category instances. It contains three proved private
helpers: `sectionsDerives`, `sectionsPairExists`, `sectionsTowerGrothendieck`.
`end Generic` precedes the existing `SequenceCoefficientRestrictionData` definition.
The generic tower-comparison helper is in a second scoped section `GenericTower`,
with fresh derived-category universes `dtA dtD` and abstract abelian categories.
The abstract scalar helpers explicitly take the target derived-category instance.
A third scoped section `GenericScalar` proves composition of derived-unit
comparisons for three abstract abelian categories. The concrete scalar cocycle
specializes it. All later added helpers, including the generic
composition-normalization and inverse-cocycle calculations, are private. The proof
locally marks `Functor.mapDerivedCategory` irreducible and uses its factorization API;
this local setting does not change exported attributes. Their constructions specify
their data; none
chooses arbitrary data from an unproved existence theorem. The final public theorem
has a complete proof. The only new public theorem is in its own new Sheaf module
with its own DAG node, `lem-coef-restriction-sections-acyclic`.

## Users

Ran `tools/downstream.py Sheaf.CategoryTheory.CoefficientSequenceGlobalSections --uses
coefficientSequenceGlobalSectionsEvaluation sequenceCoefficientModules
sequenceCoefficientSections SequenceSectionsComparisons`.
All original declarations and public imports are preserved verbatim. No consumers
need adaptation; their visible interface is identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientSequenceGlobalSections | A5 | Assigned proof completed; private proof helpers and imports added. |
| Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit | unclaimed | No interface change or adaptation. |
| Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula | unclaimed | No interface change or adaptation. |
| Sheaf.CategoryTheory.ScalarHomZeroCompatibility | unclaimed | No interface change or adaptation. |

## Status

landed 20261024T184540-L-3066020 2026-10-24 (merge of deliver/A5/Sheaf.CategoryTheory.CoefficientSequenceGlobalSections)
