# AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_square_scalar_comparison

## Reason

Prove the existing theorem using the specified open adjunction, the existing module
essential-image criterion and fully faithful localization. Remove imports used only
by the longer proposed scalar-transport argument. The theorem signature and both
public comparison definitions retain their exact types and construction bodies. The module pullback comparison is
marked `@[irreducible]` to prevent expensive unfolding of the pullback mates and
categorical unification. The complex comparison keeps its original reducibility and is used by definitional conversion. This is a transparency
repair only; the objects, maps, and equations represented by both definitions are unchanged. Public imports needed for their
statements and definitions are retained; proof dependencies are private imports.
The proof uses local elaboration options for transparency and instance size;
these add no declarations or instances. The proof also marks the abelian comparison
definitions `upperStarCongr`, `upperStarCompIso` and `upperStarFromPointComp`
locally irreducible. These local attributes do not affect importers or modify the
adopted source modules. Generic helper proofs unfold the definitions explicitly.

## Old

Both comparison definitions have the default reducibility status.

```lean
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
public import Sheaf.CategoryTheory.ExactDerivedComposition
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.CartesianCoefficients
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
```

## New

The module pullback comparison gains `@[irreducible]`; both types and bodies are unchanged.

```lean
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Sheaf.Paper.ProfinitePointPullback
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
```

## Users

`python3 tools/downstream.py Sheaf.Paper.CondensedOpenSquareScalarComparison
--uses AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_square_scalar_comparison`
reports zero downstream modules and only the defining module as a textual user.
A direct import/name search agrees. The unfinished DAG parent remains attached to
this node; neither its dependency nor the enclosing unit route changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedOpenSquareScalarComparison | U9 | Existing types and construction bodies unchanged; module pullback comparison made irreducible, theorem proved and unused imports removed. |

## Status

landed 20261024T020809-L-2668101 2026-10-24 (merge of deliver/U9/Sheaf.Paper.CondensedOpenSquareScalarComparison)
