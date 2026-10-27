# WeilConjectures.sixFunctorProjectionFiniteReductionSquare

## Reason

The finite coherence proof compares derived tensor endpoints and pullback constructions at
concrete coefficient categories. Unfolding the raw bifunctor evaluations and monoidal
associators there causes repeated large conversions during elaboration and kernel checking.
The square now uses the existing coefficient-generic tensor-coordinate evaluation and the
existing named associator. These are the same canonical proper/open projection and tensor
associator, exposed before coefficient specialization.

The theorem sixFunctorProjection_reduction_finite keeps its original signature. The datum's
upper component is still sixFunctorProjectionFiniteInFixedCoordinates, whose original
realization-conjugation definition is retained verbatim. The ideal is arbitrary, and the
lower projection remains on the ambient derived category, including nonperfect quotients.
The meaning review for any target using the definition reopens under AGENTS.md section 4.
No Challenge declaration changes.

## Old

```lean
def sixFunctorProjectionFiniteReductionSquare (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left)
    (J : Ideal (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  let RY := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X
  let TY := CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) Y
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  let U := CompactSupportFiniteProjection.fixedDerivedPull (C := C) (E := E) (n := n) f
  let k := RX.inverse.obj K.obj
  let q := RY.inverse.obj L.obj
  let N := DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((constantSheaf (ProEt.topology Y.obj.left) (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A (A ⧸ J))))
  (TY.flip.obj N).map (sixFunctorProjectionFiniteInFixedCoordinates S f c K L) ≫
      CompactSupportFiniteProjection.fixedComponent (C := C) (E := E) (n := n) (hn := hn)
        f c ((TX.obj k).obj (U.obj q)) N =
    (MonoidalCategory.associator (F.obj k) q N).hom ≫
      CompactSupportFiniteProjection.fixedComponent (C := C) (E := E) (n := n) (hn := hn)
        f c k ((TY.obj q).obj N) ≫
      F.map ((TX.obj k).map
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso
          (ModuleCat.{u + 1} A) f.hom.left q N).hom)) ≫
      F.map (MonoidalCategory.associator k (U.obj q) (U.obj N)).inv
```

## New

```lean
def sixFunctorProjectionFiniteReductionSquare (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left)
    (J : Ideal (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) : Prop :=
  -- Construct the equation before specializing its coefficient instances.
  let square (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
      [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
      [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
      [UpperStarPreservesFlat A]
      {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
      (k : DerivedCategory (Sheaf (ProEt.topology X) A))
      (q N : DerivedCategory (Sheaf (ProEt.topology Y) A))
      (v : ((derivedTensor A Y).obj
          ((rightDerivedLowerShriekOfCompactification A c).obj k)).obj q ⟶
        (rightDerivedLowerShriekOfCompactification A c).obj
          (((derivedTensor A X).obj k).obj ((upperStar A f).leftDerivedFunctor.obj q))) :=
    let TX := derivedTensor A X
    let TY := derivedTensor A Y
    let F := rightDerivedLowerShriekOfCompactification A c
    let U := (upperStar A f).leftDerivedFunctor
    (TY.flip.obj N).map v ≫
        projectionTensorCoordinateComponent A c ((TX.obj k).obj (U.obj q)) N =
      (projectionActionAssociator A Y (F.obj k) q N).hom ≫
        projectionTensorCoordinateComponent A c k ((TY.obj q).obj N) ≫
        F.map ((TX.obj k).map (leftDerivedUpperStarTensorIso A f q N).hom) ≫
        F.map (projectionActionAssociator A X k (U.obj q) (U.obj N)).inv
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  let RY := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Y
  let k := RX.inverse.obj K.obj
  let q := RY.inverse.obj L.obj
  let N := DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((constantSheaf (ProEt.topology Y.obj.left) (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A (A ⧸ J))))
  square (ModuleCat.{u + 1} A) f.hom.left c k q N
    (sixFunctorProjectionFiniteInFixedCoordinates S f c K L)
```

The square's equation is constructed in a local generic coefficient-category function,
then specialized to the same ModuleCat category and the actual conjugated component.
This freezes its tensor, pullback and support instances before coefficient specialization;
no new public declaration or mathematical object is introduced. The generic function
retains exactly the displayed equation. Profiling located repeated conversions in the
previous concretely elaborated equation; the staged version compiles within the limit.

The tensor aliases are derivedTensor; fixedTensor already calls that same construction.
The compact-support alias uses rightDerivedLowerShriekOfCompactification, whose body is
the same extension-by-zero followed by right-derived direct image as sfFixedCompactSupport.
The inverse image remains fixedDerivedPull, with its generic instance construction recorded
in V5-fixed-derived-pull-braiding.md. The existing public equality
projectionTensorCoordinateComponent_eq identifies each lower component with the published
projectionMapOfCompactification evaluation. projectionActionAssociator is exactly the
canonical derived tensor associator.

The finite proof first cancels the actual source and target realization comparisons using
the existing sixFunctorProjection_realization equation. A proved equivalence-preimage lemma
identifies the conjugated arrow with fixedComponent. A private proved coordinate equation
then uses explicit equality of three coefficient property instances before reflexivity, keeping
large instance terms out of conversion. Its references to stored auxiliary proofs are
confined to this theorem proof; public signatures and definition bodies contain none.

A private generic adapter applies the existing compactification tensor-action identity and
preservation of composition by the compact-support functor. Coordinate definitions are
unfolded directly, avoiding extra equality transports. This conversion is done before
coefficient specialization. The finite proof applies it with the degree-zero constant A/J.
No flatness or perfectness of A/J is assumed.

FiniteProjectionActionLaws is imported publicly because the square uses its public named
associator. Private import-all commands expose the existing generic proved action theorem
and the three already-proved stored instance proofs. All new proof scopes respect both
transparency options. Named functors are kept irreducible only in the conversion-sensitive
proof scope; no global instance, definition attribute, time limit or heartbeat limit changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Same finite square and theorem signature; canonical endpoint presentation and finite reduction proof. |

There are no external direct users of sixFunctorProjectionFiniteReductionSquare in the
current source. Its definition and the finite reduction theorem are both in this module.
The existing node and all unfinished parent dependencies remain attached. The node records
the general proper/open tensor-action calculation as the finite clause's tool.

## Status

landed 20261026T071400-L-3922877 2026-10-26 (merge of deliver/V5/Sheaf.Paper.ProjectionFormulaCoherence)
