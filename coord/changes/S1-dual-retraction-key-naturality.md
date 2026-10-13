# AlgebraicGeometry.Scheme.Modules.dual_retraction_key

## Reason

The original family e was arbitrary. Naturality does not follow from being an
isomorphism. The proof plan explicitly assumes it without recording a hypothesis.
For U=X over Spec(Q), take P=Q a free rank-two sheaf, f the basis swap, and s its
inverse. Modify the comparison on the dual by diag(2,1). The composite is a
nontrivial commutator, rather than the identity: in column-vector convention,
with S the swap matrix and D=diag(2,1), it is D⁻¹ S D S=diag(1/2,2).
Choose the usual comparison at every other pair (A,B); no naturality is required
in the old statement, so this modification is allowed. The corrected theorem requires
the naturality that the source argument's restriction comparison has.

## Old

```lean
theorem dual_retraction_key
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) (U : X.Opens)
    (s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P)
    (e : ∀ A B : X.Modules,
      (restrictFunctor U.ι).obj (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf)
          ((restrictFunctor U.ι).obj A) ((restrictFunctor U.ι).obj B))
    (hs : s ≫ (restrictFunctor U.ι).map f = 𝟙 _) :
    (restrictFunctor U.ι).map (dualMap f) ≫
        (e P (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
          s (𝟙 _) ≫ (e Q (SheafOfModules.unit X.ringCatSheaf)).inv = 𝟙 _
```

## New

```lean
theorem dual_retraction_key
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) (U : X.Opens)
    (s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P)
    (e : ∀ A B : X.Modules,
      (restrictFunctor U.ι).obj (SheafOfModules.homObj
        (R := X.sheaf) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf)
          ((restrictFunctor U.ι).obj A) ((restrictFunctor U.ι).obj B))
    (he : ∀ {A A' B B' : X.Modules} (a : A' ⟶ A) (b : B ⟶ B'),
      (restrictFunctor U.ι).map
          (SheafOfModules.homObjMap (R := X.sheaf) a b) ≫
        (e A' B').hom = (e A B).hom ≫
          SheafOfModules.homObjMap (R := U.toScheme.sheaf)
            ((restrictFunctor U.ι).map a) ((restrictFunctor U.ι).map b))
    (hs : s ≫ (restrictFunctor U.ι).map f = 𝟙 _) :
    (restrictFunctor U.ι).map (dualMap f) ≫
        (e P (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          s (𝟙 _) ≫ (e Q (SheafOfModules.unit X.ringCatSheaf)).inv = 𝟙 _
```

The X.sheaf and U.toScheme.sheaf spellings are definitionally equal to the old
ringed-space sheaves. No construction or target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DualRetractionKey | S1 | Add naturality and prove cancellation. |
| Sheaf.AlgebraicGeometry.Modules.DualRetractionOfLocalSection | unclaimed | Pass the existing he argument. Statement and visibility identical. |

`tools/downstream.py ... --uses AlgebraicGeometry.Scheme.Modules.dual_retraction_key`
reports exactly these two direct declaration users. The transitive import
users other than the caller do not reference the changed theorem; the caller's statement is unchanged,
so they require no adaptation and no target statement or definition changes.

The original caller against the changed dependency fails at line 45: hs has type
`s ≫ F.map f = 𝟙 _` but a naturality equation is expected. The only changed line is
`exact dual_retraction_key f U s e he hs`, using the he already bound at line 39.
This is forced by the added binder; no other caller lines are changed.

## Status

landed 20261013T222413-L-1226536 2026-10-13 (merge of deliver/S1/Sheaf.AlgebraicGeometry.Modules.DualRetractionKey)
