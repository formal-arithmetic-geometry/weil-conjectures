# Finite left-route prefix and tensor transport

## Reason

Separate the proved projection/exchange prefix from the strictly smaller final tensor normalization, keeping the original theorem and all definitions unchanged.

## Old

Both declarations are new; no previous signature is replaced.

## New

```lean
theorem sixFunctorProjectionFinite_left_prefix
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj
      ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)
    let d := sixFunctorProjectionFiniteTensorRealization S Q.X K
        ((torPull S.toSixFunctorFiniteOperations Q.f).obj L) ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
    let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
      R'.functor.mapIso (F.mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ U.mapIso d))
    I.map ((S.finite.pull Q.g).map
        (component S.toSixFunctorFiniteOperations Q.f Q.compactification K L)) ≫
      I.map (sixFunctorProjectionFiniteExchange S Q M) ≫ mid.hom =
    (sixFunctorProjectionFiniteSquareSource S Q K L).hom ≫ R'.functor.map
      ((FiniteProjectionExchange.pull A Q.g.hom.left).map
          (FiniteProjectionExchange.pf A Q.compactification
            (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) ≫
        FiniteProjectionExchange.ex A Q.square Q.compactification
          (FiniteProjectionExchange.tensor A Q.X.obj.left (RX.inverse.obj K.obj)
            ((FiniteProjectionExchange.pull A Q.f.hom.left).obj (RY.inverse.obj L.obj))))
```

```lean
theorem sixFunctorProjectionFinite_left_tensor_transport
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj
      ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)
    let d := sixFunctorProjectionFiniteTensorRealization S Q.X K
        ((torPull S.toSixFunctorFiniteOperations Q.f).obj L) ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
    let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
      R'.functor.mapIso (F.mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ U.mapIso d))
    I.map ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map
      ((sixFunctorProjectionFiniteMu S Q.g' K
          ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)).hom ≫
        ((partialTensor S.toSixFunctorFiniteOperations Q.X').obj
          ((S.finite.pull Q.g').obj K)).map
          ((torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
            ObjectProperty.homMk (eqToHom (congrArg
              (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj)
              Q.squareComm)) ≫
            (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom))) ≫
      (sixFunctorProjectionFiniteSquareTarget S Q K L).hom =
    mid.hom ≫ R'.functor.map (F.map
      (FiniteProjectionExchange.target A Q.square (RX.inverse.obj K.obj)
        (RY.inverse.obj L.obj)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion | D6 | Proof imports the two new equations and pastes them; original signature unchanged. |

## Status

landed 20261028T034726-L-3537944 2026-10-28 (merge of deliver/D6/Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion)
