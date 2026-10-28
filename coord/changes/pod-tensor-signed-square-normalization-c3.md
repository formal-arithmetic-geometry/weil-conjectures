# WeilConjectures.podReindexingTensorSignedShifts_tensorSquares

## Reason

The original theorem asserts compatibility for arbitrary source and target shift
isomorphisms. PodTensorSignedShift is data, and neither its Generators nor its
Model property is automatic. Changing just the target left isomorphism by a sign
breaks the square on a nonzero completed tensor object, already for g=id and r=0.
The paper uses the signed, representative-normalized shifts. Add their four laws,
which the only caller already obtains from its core construction.

## Old

```lean
theorem podReindexingTensorSignedShifts_tensorSquares
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X) :
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.left M N M' r a).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M' N).hom ≫
          (SX.left ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible M'⟩ r
            ((podOrdinaryReindex l E g).mapIso a ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app M.obj)).hom)) ∧
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.right M N N' r b).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M N').hom ≫
          (SX.right ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible N'⟩ r
            ((podOrdinaryReindex l E g).mapIso b ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app N.obj)).hom))
```

## New

```lean
theorem podReindexingTensorSignedShifts_tensorSquares
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (hSY : SY.Generators l E) (hSX : SX.Generators l E)
    (mSY : SY.Model l E D.shiftSource) (mSX : SX.Model l E D.shiftTarget) :
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.left M N M' r a).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M' N).hom ≫
          (SX.left ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible M'⟩ r
            ((podOrdinaryReindex l E g).mapIso a ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app M.obj)).hom)) ∧
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.right M N N' r b).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M N').hom ≫
          (SX.right ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible N'⟩ r
            ((podOrdinaryReindex l E g).mapIso b ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app N.obj)).hom))
```

The conclusions and all original binders are retained. Four normalization proofs
are added. The only caller passes its already available h₅, h₆, h₇ and h₈; its
own signature and conclusion remain identical. No Challenge declaration or
shared definition changes. The item now reduces the corrected statement to a
strict tower calculation and a separate Roos path normalization; these assert
strictly different parts of the source argument and have separate modules/nodes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReindexingTensorSignedSquares | C3 | Repaired statement; proof by normalized paths and isomorphism cancellation. |
| Sheaf.Paper.PodReindexingTensorSignedShifts | unclaimed at inspection | Pass the four laws produced by its existing core theorem. No signature or other proof line changes. |

The source search and downstream.py --uses found no other caller. The node
lem-pod-reindexing-tensor-signed-shifts remains valid: its core step already
provides exactly these normalizations. Indirect consumers see its unchanged
statement. No target meaning is changed by a definition change.

The counterfactual single-file compile confirms necessity: with the corrected
item, the original parent fails at line 77 on hs.1 and hs.2 with "Invalid
projection: Projections cannot be used on functions". It awaits precisely the
four added law proofs. The one-line adapted parent compiles in 5.9 seconds.

## Status

landed 20261028T020229-L-2482936 2026-10-28 (merge of deliver/C3/Sheaf.Paper.PodReindexingTensorSignedSquares)
