# Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit

## Reason

Prove the existing comparison theorem and prune imports which its public declarations
do not require. The proof uses private generic derived-functor and Roos helpers in a
scoped section. No existing declaration signature, visibility, definition, or instance
body changes. No target statement or definition changes. This record covers the
public-import and section-command changes flagged by stage-3 preflight.

## Old

The original imports, verbatim:

```lean
public import Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
```

The original namespace prelude, verbatim:

```lean
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
```

All existing signatures and non-theorem bodies following this prelude are preserved
verbatim in the delivery. Only the final theorem's proof and proof docstring change.

## New

```lean
public import Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
import Sheaf.CategoryTheory.SystemGrothendieck
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Sheaf.Algebra.Homology.ExactProductsRoosComparison
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
```

The namespace prelude remains as above. It is followed by this scoped helper prelude:

```lean
section Generic

universe a av b bv c cv da db dc sep
variable {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{da} E]
  {F : Type b} [Category.{bv} F] [Abelian F] [HasDerivedCategory.{db} F]
  {H : Type c} [Category.{cv} H] [Abelian H] [HasDerivedCategory.{dc} H]
```

Every added helper is private and proved. `end Generic` precedes the existing
site variables. Local `omit` commands restrict helper hypotheses. The private
`sectionsRestrictionIso` definition is marked irreducible to control elaboration;
no public declaration receives that attribute. These commands do not change any
existing declaration's elaborated signature. The two removed public imports are
unnecessary for the module's public signatures and definitions. The homotopy-limit
module remains a private proof import; RingedToposMorphism is unused directly.

## Users

Ran:

```
python3 tools/downstream.py Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit --uses coefficientSequenceSectionsLimitComparison sequenceSectionsLimitOrdinary sequenceProjectionDirectImage
```

Result: zero downstream modules. Each of the three declaration-use searches lists
only the item itself. No consumer adaptations are necessary. DAG parents with
unfinished proofs still need this item; neither it nor any dependency is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit | N1 | Existing signatures and definitions unchanged; theorem proved; private helpers and proof imports added; unused public imports pruned. |

## Status

landed 20261021T143928-L-22695 2026-10-21 (merge of deliver/N1/Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit)
