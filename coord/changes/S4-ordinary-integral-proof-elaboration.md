# WeilConjectures.ordinaryIntegralCompletionComparison

## Reason

The stage-3 static gate classifies new module-level attribute commands as changes to what
importers see and requires this record. The mathematical interfaces are unchanged: no public
statement, public definition body, or public import changes. The new controls suppress
competing imported instance presentations and prevent unnecessary unfolding after the
corresponding construction or naturality proof has been checked. Without these controls,
the filled proofs can exceed the existing 60-second compile limit. No limit is raised.

The same controls apply to the completed ring map, module pullback, strict cone map, and
constructed private comparison. This records the entire module command change, rather than
claiming that it is an additional mathematical hypothesis or a different coefficient object.

## Old

The original elaboration preamble, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

The original public completion-comparison definition, verbatim:

```lean
def ordinaryIntegralCompletionComparison :
    ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f :=
  (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose
```

None of the additional attribute commands below appeared in the original file.

## New

The new elaboration preamble, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
```

The public definition retains its original body. Its later local transparency command is:

```lean
def ordinaryIntegralCompletionComparison :
    ordinaryIntegralDerivedPull l E f ⟶ integralDerivedPullback l E f :=
  (ordinaryIntegralCompletionComparison_existsUnique l E f).exists.choose

attribute [local irreducible] ordinaryIntegralCompletionComparison
```

The other new local attribute commands, each placed after the necessary construction or
proof, are verbatim:

```lean
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
attribute [local irreducible] limit
attribute [local irreducible] ordinaryIntegralDirectRingMap
attribute [local irreducible] ordinaryIntegralModulePull
attribute [local irreducible] towerTransitionEndomorphism
attribute [local irreducible] ordinaryIntegralCompletionChain
  integralOperationsPullbackComplexFunctor integralDerivedPullback integralDerivedPullbackComparison
attribute [local irreducible] ordinaryIntegralComparisonOnGood
```

The private generic Roos naturality lemma uses the following declaration-scoped settings;
the module defaults remain as recorded in the preamble:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

## Users

The current `tools/downstream.py` check reports one downstream module,
`Sheaf.Paper.OrdinaryPullbackStratifiedModels`. It imports the ordinary construction and
uses `ordinaryIntegralDirectRingMap`, `ordinaryIntegralModulePull`, the ordinary derived
functor, and its computation counit. It does not use `ordinaryIntegralCompletionComparison`.
Every signature, public definition body and public import it sees is preserved.
The return repair adds only proved private sheafification lemmas and removes one proof
import; no consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | S4 | Five proof holes closed; compiler controls documented above; repaired coefficient-naturality import. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | unclaimed | Same public declarations and imports; no adaptation. |

No other module is adapted. The ordinary-pullback models module was added after the
original retained packet's zero-importer census. The repair preserves its dependency and
the current main-node proof route that cites it. No source-library module, declaration
signature, attribute, or public import is edited by this delivery.

## Status

landed 20261021T130143-L-2567661 2026-10-21 (merge of deliver/S4/Sheaf.Paper.OrdinaryCompletedIntegralPullback)
