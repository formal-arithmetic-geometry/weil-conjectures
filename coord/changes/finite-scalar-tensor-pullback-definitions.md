# finiteScalarPullbackComparison and finiteScalarCurriedTensorPullback

## Reason

The representative square must refer to the exact existing pullback comparisons without
importing the theorem that will be proved from that square. Move the two definitions to
Sheaf.Paper.FiniteScalarPullbackComparison and publicly re-export that module from the
original item. Both declaration names, signatures, attributes and defining terms are
preserved. Only their docstring blueprint attachment is moved to the new definition node.
The original node lem-sf-finite-scalar-tensor-pullback-comparison now lists
def-sf-finite-scalar-pullback-comparison among its statement dependencies. This records
the relocation only: its mathematical statement and Lean theorem signature are unchanged.
No adopted source-library module changes.

## Old

In Sheaf.Paper.FiniteScalarTensorPullbackComparison:

```lean
def finiteScalarPullbackComparison (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfIntrinsicDerivedEquivalence Y R).functor ⋙
        proEtaleConstantRingDerivedPullback R p ≅
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctor ⋙
        (sfIntrinsicDerivedEquivalence X R).functor := by
  let a := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingDerivedAdjunction p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
    (proEtaleConstantRingComparison p R)
  have hρ : proEtaleRingDirectImageMap p (proEtaleConstantRing Y R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R) =
      proEtaleCoefficientDirectImageMap p R := by
    change (proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
      (proEtaleCoefficientInverseImageMap p R) = _
    exact ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hg : proEtaleConstantRingPushforward R p =
      proEtaleConstantModuleDirectImage p R := by
    unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
      proEtaleConstantModuleDirectImage
    rw [hρ]
  let r := (sfIntrinsicDerivedDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft (sfIntrinsicDerivedEquivalence X R).functor
      (Functor.rightDerivedFunctorNatIso (eqToIso hg)).symm
  let α := ((mateEquiv a b).symm
    (TwoSquare.mk _ (sfIntrinsicDerivedEquivalence X R).functor
      (sfIntrinsicDerivedEquivalence Y R).functor _ r.hom)).natTrans
  have : IsIso α := isIso_inverseMate_of_equivalences a b r
  exact asIso α

def finiteScalarCurriedTensorPullback (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R)) :
    (postcompose₂.obj (proEtaleConstantRingDerivedPullback R p)).obj
        (curry.obj aY.tensor) ⟶
      (((whiskeringLeft₂ _).obj (proEtaleConstantRingDerivedPullback R p)).obj
        (proEtaleConstantRingDerivedPullback R p)).obj (curry.obj aX.tensor) :=
  curry.map (proEtaleCanonicalTensorComparison p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
    (proEtaleConstantRingComparison p R) aY aX).hom ≫
      (curryObjProdComp (proEtaleConstantRingDerivedPullback R p)
        (proEtaleConstantRingDerivedPullback R p) aX.tensor).hom
```

## New

Exactly the signatures and defining terms displayed in Old, now in
Sheaf.Paper.FiniteScalarPullbackComparison. The original module publicly imports it.
There is no change to the mathematical objects or to target meanings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteScalarTensorPullbackComparison | W7 | Publicly re-exports both definitions; proves its original theorem using the new normalized tensor construction. |
| Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives | W7 (new module) | States the fixed-pair square with the unchanged comparison definitions. |
| Sheaf.Paper.FiniteScalarProperProjectionPresentation | unclaimed in current claim records | Same names, signatures and reducible bodies remain available through the original import; no adaptation expected. |

The downstream script finds 130 transitively importing modules; its declaration-use
filter and repository search find only the two existing users in this table; the new representative module is listed as well. The direct importer
is compiled against this delivery and its unchanged copy is excluded from the packet.

## Status

landed 20261027T103523-L-1098311 2026-10-27 (merge of deliver/W7/Sheaf.Paper.FiniteScalarTensorPullbackComparison)
