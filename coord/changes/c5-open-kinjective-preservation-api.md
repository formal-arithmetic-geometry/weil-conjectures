# AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_inverseImage_isKInjective

## Reason

Profiling found costly kernel conversions in registering the concrete complex-level
instances, and in the large OpenCube structure. Factor the existing complete open
preservation proof through functor-level preservation instances and compile the
unchanged cube definitions in a separate module. This keeps each file within the
60 second limit. No existing declaration is removed, no mathematical assertion is
weakened, and no source-library file changes.

## Old

```lean
@[instance] theorem open_inverseImage_isKInjective {S Z : Scheme.{u}} (j : S ⟶ Z)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ R')
    (I : CochainComplex (proEtaleRingModules Z R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((proEtaleRingModulePullback j R R' c).mapHomologicalComplex (.up ℤ)).obj I)

@[instance] theorem open_upper_isKInjective (r : StrictTowerRingedSquare sq)
    [IsOpenImmersion g] (I : CochainComplex (proEtaleRingModules X r.RX) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((upperPull r).mapHomologicalComplex (.up ℤ)).obj I)
```

Both declarations were complex-level instances in the item. The item also defined
OpenCube and its sourceFace, targetFace, baseFace and upperFace directly.

## New

```lean
public import Sheaf.AlgebraicGeometry.RingedUpperOpenPullbackKInjective
public import Sheaf.AlgebraicGeometry.RingedRestrictionOpenCube

theorem open_inverseImage_isKInjective {S Z : Scheme.{u}} (j : S ⟶ Z)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ R')
    (I : CochainComplex (proEtaleRingModules Z R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((proEtaleRingModulePullback j R R' c).mapHomologicalComplex (.up ℤ)).obj I)

theorem open_upper_isKInjective (r : StrictTowerRingedSquare sq)
    [IsOpenImmersion g] (I : CochainComplex (proEtaleRingModules X r.RX) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((upperPull r).mapHomologicalComplex (.up ℤ)).obj I)
```

The two existing named theorem signatures are retained; their instance attributes
are replaced by these fully proved functor-level instances:

- open_pullback_preservesKInjectiveComplexes in ProEtaleOpenPullbackKInjective;
- upper_pull_preservesKInjectiveComplexes in RingedUpperOpenPullbackKInjective.

The latter publicly imports the former. The library's generic complex-map instance
then supplies the same K-injective inference for any complex. The original proof
is generalized from one complex to all complexes, with no extra assumption. It
still uses localized restriction, the open-site equivalence and the scalar
isomorphism comparison. No arbitrary data are chosen from mere existence.

OpenCube and all four face definitions move verbatim, including every field and
coherence requirement, into RingedRestrictionOpenCube. Only their blueprint
ownership docstring changes. The item publicly imports that module. Their names,
visibility, signatures, bodies and reducibility are retained. The new definition
node owns these five declarations; the original node depends on that owner.

Six proof imports move from the item to ProEtaleOpenPullbackKInjective: the private
ProEtaleOperations import, ScalarExtensionRingIso, RightDerivedFunctor.FullyFaithful,
ProEtaleRingedOpenComparison, RingedDerivedRestrictionGeneral, and
KInjectiveRestrictLocalizedOfUniverses. These mathematics dependencies are retained.
The item no longer restores all its local irreducibility settings after degree-zero
normalization: only proEtaleRingModuleDirectImage becomes locally semireducible,
as needed by the identity direct-image proof. No exported reducibility attribute
changes. Generic two-isomorphism cancellation also shortens the existing
open_representative proof without changing its signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent | C5 | Named complex-level theorems retain their types; inference uses functor preservation. Cube definitions are publicly re-exported. |

The downstream-use tool reports zero downstream modules, and direct-import
search finds none. Uses of both named preservation theorems are confined to the
item. Thus there are no unchanged Lean importers to compile or adapt. The four
DAG citers listed in report.md retain the same assertions: the definitions and
all mathematical hypotheses are identical. The original item itself compiles
using the new preservation inference in open_representative. No forced adaptation
of another group's module is required.

## Status

landed 20261026T222602-L-670542 2026-10-26 (merge of deliver/C5/Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent)
