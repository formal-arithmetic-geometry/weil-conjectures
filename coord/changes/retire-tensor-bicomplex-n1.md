# HomologicalComplex₂.tensorBicomplex, tensorBicomplexMap and chainTensorMap

## Reason

Complete the listed retirement of Sheaf.Algebra.Homology.TensorBicomplex
(coord/retire-items.tsv). The item has zero holes. The two unsigned bicomplex
aliases already exist verbatim in the adopted upstream TensorBicomplexExtension;
the chainTensorMap construction already exists as ChainComplex.tensorMap in
upstream TensorBicomplex. No current Lean source imports the Sheaf module or
uses chainTensorMap. The historical queue's single consumer has already migrated.
Withdraw the unused duplicate and redirect its DAG attachment to the retained
upstream extension, which publicly imports the chain-map construction.

## Old

The retired module contained these declarations (verbatim):

```lean
abbrev tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P).obj Q

/-- Compatibility abbreviation for the canonical Mathlib bifunctor map.
A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  dsimp% only [Functor.uncurry] (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)

/-- The tensor of a chain map with a module map, formed by mapping the chain map
and then the module map.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
def chainTensorMap {P P' : ChainComplex (ModuleCat.{u} R) ℕ}
    {N N' : ModuleCat.{u} R} (a : P ⟶ P') (g : N ⟶ N') :
    ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P ⟶
      ((tensorRight N').mapHomologicalComplex (.down ℕ)).obj P' :=
  -- Canonical composite of the two induced chain maps.
  ((tensorRight N).mapHomologicalComplex (.down ℕ)).map a ≫
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
      (.down ℕ)).app P'
```

## New

Withdraw lean/Sheaf/Algebra/Homology/TensorBicomplex.lean through deleted.txt.
No replacement definition is introduced. The node's existing Lean attachment
names HomologicalComplex₂.tensorBicomplex and tensorBicomplexMap in
WeilConjectures.Algebra.Homology.TensorBicomplexExtension, and ChainComplex.tensorMap
from its public import WeilConjectures.Algebra.Homology.TensorBicomplex.
The latter has precisely the old chainTensorMap signature and composite body.
All upstream signatures, attributes, public imports and bodies remain untouched.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.TensorBicomplex | N1 | Withdraw the unused duplicate. |
| WeilConjectures.Algebra.Homology.FlatResolutionTorComparison | unclaimed | Already imports upstream TensorBicomplex and TensorBicomplexExtension; unchanged. |

An exact import search through lean/Sheaf and lean/WeilConjectures finds no
importer of the withdrawn module. There are no adaptations. The formerly named
Sheaf.Algebra.Homology.FlatResolutionTorComparison is already absent.
No target statement or definition used by a target changes meaning. The
node's statement, dependencies, source and unit route stay unchanged.

The scratchpad/Upstream__probe.lean server check proves by rfl that both retained
bicomplex aliases equal the old canonical expressions and ChainComplex.tensorMap
equals the old composite. #print axioms on all three reports only propext,
Classical.choice and Quot.sound. It compiled successfully in 1.2 seconds.
The scratch probe is verification evidence, not a delivered library module.

## Status

landed 20261020T132019-L-1402004 2026-10-20 (merge of deliver/N1/Sheaf.Algebra.Homology.TensorBicomplex)
