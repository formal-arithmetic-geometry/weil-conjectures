# WeilConjectures.sixFunctorProjectionFiniteMu

## Reason

The finite base-change theorem must compare the two ordered routes with the existing
fixed-scalar projection diamond. Put its coordinate definitions in an independent
module so that the separate route-realization theorem can be stated without importing
its consumer. This is a definition relocation, with the existing names, signatures,
visibility and bodies preserved verbatim. The item publicly reexports the new module.
No choice of a map, tensor comparison, or exchange is changed.

## Old

In `lean/Sheaf/Paper/ProjectionFormulaCoherence.lean`:

```lean
/-- Inverse realization of the finite partial tensor, with its coefficient unit cancelled.
Source: current blueprint prop-sf-pf-coherence, tensor identifications
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteTensorRealization (_S : SixFunctorDatum D C E n hn)
    (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :=
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  (R.unitIso.app
    (((CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X).obj
      (R.inverse.obj K.obj)).obj (R.inverse.obj L.obj))).symm

/-- Monoidality on the finite partial-tensor domain, in the datum's operation coordinates.
Source: current blueprint prop-sf-pf-coherence, vertical tensor comparison
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (S.finite.pull f).obj
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).obj
        K).obj L) ≅
    ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
      ((S.finite.pull f).obj K)).obj
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations f).obj L) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  let RY := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X
  let U := CompactSupportFiniteProjection.fixedDerivedPull (C := C) (E := E) (n := n) f
  ObjectProperty.isoMk _
    (CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations f
      (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).obj
        K).obj L) ≪≫
      RX.functor.mapIso
        ((CompactSupportFiniteProjection.fixedPullComparison
          (C := C) (E := E) (n := n) f).symm.app _ ≪≫
          U.mapIso (sixFunctorProjectionFiniteTensorRealization S Y K L) ≪≫
          AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
            f.hom.left (RY.inverse.obj K.obj) (RY.inverse.obj L.obj) ≪≫
          (TX.mapIso
            (CompactSupportFiniteProjection.fixedPullRealization
              S.toSixFunctorFiniteOperations f K).symm).app _ ≪≫
          (TX.obj _).mapIso
            (CompactSupportFiniteProjection.fixedPullRealization
              S.toSixFunctorFiniteOperations f ⟨L.obj, L.property.1⟩).symm))

/-- The A2 finite exchange in the actual bounded constructible operation coordinates.
The target uses the Cartesian base change of the chosen compactification; arbitrary
choices are compared by sixFunctorProjection_compactification.
Source: current blueprint prop-sf-pf-coherence, Ex_! vertical arrow
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteExchange (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D) (K : sixFunctorFiniteCategory D C E n hn Q.X) :
    (S.finite.pull Q.g).obj ((S.finite.support Q.f Q.compactification).obj K) ⟶
      (S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).obj
        ((S.finite.pull Q.g').obj K) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let U := sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) Q.g.hom.left
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  ObjectProperty.homMk
    ((CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations Q.g
      ((S.finite.support Q.f Q.compactification).obj K)).hom ≫
      R.functor.map (U.map (CompactSupportFiniteProjection.fixedSupportRealization
        S.toSixFunctorFiniteOperations Q.f Q.compactification K).hom) ≫
      R.functor.map
        ((CompactSupportFiniteProjection.fixedPullComparison
          (C := C) (E := E) (n := n) Q.g).inv.app _) ≫
      (S.finiteExchangeProjection Q).2.1.app K ≫
      R.functor.map (F.map (CompactSupportFiniteProjection.fixedPullRealization
        S.toSixFunctorFiniteOperations Q.g' K).inv) ≫
      (CompactSupportFiniteProjection.supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)).inv)
```

## New

The preceding three definitions, with exactly the same text, are in
`lean/Sheaf/Paper/ProjectionFiniteBaseChangeCoordinates.lean`.
The original module reexports them through:

```lean
public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
```

The new module additionally constructs the two routes and their common endpoint
comparisons from the existing coefficient equivalence units and support/pullback
realization isomorphisms. These definitions contain no postponed proof or arbitrary
existence choice. The overlapping `IntegralHom.derivedCategory` instance is removed
from the elaboration context of the finite base-change modules and the item, as in the existing
finite projection reduction modules; their statements use the same standard
derived-category instances. The two new endpoint comparison definitions have explicit
return types and are marked irreducible to avoid expanding their large composites
when they are used. No existing definition changes reducibility.

## Users

`python3 tools/downstream.py Sheaf.Paper.ProjectionFormulaCoherence --uses
sixFunctorProjectionFiniteTensorRealization sixFunctorProjectionFiniteMu
sixFunctorProjectionFiniteExchange` reports no downstream modules. A separate direct
import search of both `lean/` and `quarantine/` also finds none.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaCoherence | J4 | Same three definitions via public reexport; finite square is proved from route realization and the canonical diamond. |
| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | J4, new | Owns the three unchanged definitions and constructs the coordinate paths. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | J4, new | Uses the explicit routes and endpoint isomorphisms. |
| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | J4, new | Proves equality of the paths from route realization and the canonical diamond. |

## Status

landed 20261026T222721-L-685893 2026-10-26 (merge of deliver/J4/Sheaf.Paper.ProjectionFormulaCoherence)
