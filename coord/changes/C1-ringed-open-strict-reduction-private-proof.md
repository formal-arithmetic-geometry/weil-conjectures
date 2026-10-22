# cbcStrictReductionComplexIso, cbcLeftReductionComputation and cbcRightReductionComputation

## Reason

The original module has thirteen theorem holes. Completing them exposed repeated
kernel conversion of the completed coefficient category inside the endpoint maps.
The complete proof compiled in 54.6 seconds without the delivery axiom scan, but
exceeded the 60-second limit when that scan was included. The two endpoint definitions now specialize generic counit computations, and the
strict complex comparison specializes a generic degreewise construction. The
complete candidate and exact delivery axiom scan compile in 55.4 seconds.

All forty-one original public declaration signatures and all eight public imports
are preserved. The three definitions below have new bodies, definitionally equal to
the originals. All other existing non-theorem bodies are preserved verbatim.
The target statements are unchanged. Targets using these definitions are subject
to the project's renewed meaning review; the checked definitional equalities show
that the actual maps and their meaning are preserved.

## Old

```lean
def cbcStrictReductionComplexIso :=
  letI := cbcCompletedExtension_additive W d
  letI := cbcCompletedTowerExtension_additive W d
  letI := completedReductionModuleTowerFunctor_additive T d
  letI := completedReductionModuleTowerFunctor_additive W.left d
  NatIso.mapHomologicalComplex (cbcStrictReductionIso W d) (.up ℤ)

def cbcLeftReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    ((cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedReductionComplexTowerFunctor T d).obj
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (completedReductionTower T d).map
      ((cbcCompletedExtension W d).mapDerivedCategoryFactors.hom.app P) ≫
    completedReductionTowerComplexCounit T d
      (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)

def cbcRightReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    (completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((cbcCompletedTowerExtension W d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor W.left d).obj P)) :=
  (cbcCompletedTowerExtension W d).mapDerivedCategory.map
      (completedReductionTowerComplexCounit W.left d P) ≫
    (cbcCompletedTowerExtension W d).mapDerivedCategoryFactors.hom.app
      ((completedReductionComplexTowerFunctor W.left d).obj P)
```

## New

Three public definitions in this same Sheaf module supply the generic constructions.
`cbcModelComplexIso` applies a natural isomorphism degreewise. `cbcModelLeft` and
`cbcModelRight` construct the generic endpoint composites for abelian categories,
exact functors, derived reduction functors and their specified counits. They use
the existing `reductionComplexCounit`, localization factors and composition.
Their data are explicit constructions; no existence witness or new choice is used.
The completed-coefficient definitions specialize these constructions:

```lean
def cbcStrictReductionComplexIso :=
  @cbcModelComplexIso
    (reductionModules W.left (completedReductionCoefficient W.left d))
    (reductionModules T (completedReductionCoefficient T d)) _ _ _ _
    (completedReductionModuleTowerFunctor W.left d)
    (completedReductionModuleTowerFunctor_additive W.left d)
    (completedReductionModuleTowerFunctor T d)
    (completedReductionModuleTowerFunctor_additive T d)
    (cbcCompletedExtension W d) (cbcCompletedExtension_additive W d)
    (cbcCompletedTowerExtension W d) (cbcCompletedTowerExtension_additive W d)
    (cbcStrictReductionIso W d)

def cbcLeftReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    ((cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedReductionComplexTowerFunctor T d).obj
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)) :=
  @cbcModelLeft
    (reductionModules W.left (completedReductionCoefficient W.left d))
    (reductionModules T (completedReductionCoefficient T d)) _ _ _ _ _ _ _
    (completedReductionModuleTowerFunctor T d)
    (completedReductionModuleTowerFunctor_additive T d)
    (cbcCompletedExtension W d) (cbcCompletedExtension_additive W d)
    (cbcCompletedExtension_limits W d) (cbcCompletedExtension_colimits W d)
    (completedReductionTower T d) (coherenceReductionTowerCounit T d) P

def cbcRightReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    (completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((cbcCompletedTowerExtension W d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor W.left d).obj P)) :=
  @cbcModelRight
    (reductionModules W.left (completedReductionCoefficient W.left d))
    (reductionModules T (completedReductionCoefficient T d)) _ _ _ _ _ _ _
    (completedReductionModuleTowerFunctor W.left d)
    (completedReductionModuleTowerFunctor_additive W.left d)
    (cbcCompletedTowerExtension W d) (cbcCompletedTowerExtension_additive W d)
    (cbcCompletedTowerExtension_limits W d) (cbcCompletedTowerExtension_colimits W d)
    (completedReductionTower W.left d) (coherenceReductionTowerCounit W.left d) P
```

A separate Lean diagnostic imported the original published definitions,
constructed the proposed generic specializations, and proved all three equalities
by `rfl`; it compiled in 8.5 seconds. Thus the new bodies define exactly
the original morphisms, including all category and localization data. The generic
computation definitions are public because public definitions must not refer to
private helpers. Their statements need only the existing public imports.

All thirteen original theorem holes have complete proofs. The remaining new
helpers are private and proved in this same module. Five helper instances are
explicitly `private local instance`. The generic comparison is first specialized
to arbitrary ring sheaves on schemes; it packages the supplied reduction functors,
counits, universal properties and computation laws as `DerivedReductionModelData`.
This checks category conversions before instantiating the completed coefficient
limit. A curried helper also supplies the two endpoint isomorphisms. The final
public theorem is one application with explicit functor-instance proofs.

File-local instance priorities of 2000 for `reductionModulesHasDerivedCategory`
and `reductionTowerHasDerivedCategory` keep the existing standard localizations
consistent, following the existing `CompletedDirectImageLimits` precedent.
Private scalar component formulas use the explicit direct-sum carrier of the
extension presheaf. Local irreducibility attributes keep large constructions behind
proved component formulas; the final comparison's additional attributes are scoped
to its section. Additional section variables, opens and proof-elaboration options
support these constructions. No global instance or elaboration attribute is added.
No compiler or heartbeat limit is raised, and the proof stays in one file.

## Users

`tools/downstream.py Sheaf.Paper.RingedOpenStrictReduction --uses` was run for
each of the three changed definitions. Each lists only the item itself as a name user. There are
22 transitive module importers. The direct importers are included below for review;
all their existing definitions and statements keep the same meaning because all three
changed constructions are definitionally equal to their originals. No downstream
source adaptation is required or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedOpenStrictReduction | C1 | Thirteen proofs; three definitionally equal computation bodies and their generic API. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | unclaimed | Direct importer; unchanged interface and meaning. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Direct importer; unchanged interface and meaning. |
| Sheaf.Paper.CompletedOpenKFlat | unclaimed | Direct importer; unchanged interface and meaning. |

## Status

landed 20261022T023431-L-821663 2026-10-22 (merge of deliver/C1/Sheaf.Paper.RingedOpenStrictReduction)
