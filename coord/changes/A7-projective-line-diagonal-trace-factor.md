# AlgebraicGeometry.Etale.projectiveLineDiagonalTrace

## Reason

Factor the canonical chart comparison out of the trace expression and name it
`ordinaryFiniteShiftedLineChart`. This concrete comparison is used by the ordinary
Chern calculation before trace. Its body is precisely the four existing chart factors.
The old and new trace expressions are equal by associativity of composition; all
factors, their order, and the signature are preserved. No normalization is changed.
No target statement is changed. The definitions used by the target require the
usual independent statement review, with the associativity equality as evidence.

## Old

```lean
def projectiveLineDiagonalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A r).map
      (ordinaryFiniteShiftedLinePullback A N hA (projectiveLineTraceTransport N hN A hA)
        e.hom (by
          simpa using hS.map
            ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom)).hom ≫
    projectiveLineTrace N hN A hA (ProjectiveLine S)
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)
```

## New

```lean
def projectiveLineDiagonalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
  ordinaryFiniteShiftedLineChart N A hA (projectiveLineTraceTransport N hN A hA) S hS
      (projectiveLineDiagonalProjection S a) (projectiveLineDiagonalChart S a).val
      (projectiveLineDiagonalChart S a).property ≫
    projectiveLineTrace N hN A hA (ProjectiveLine S)
      (by simpa only [map_natCast] using hS.map (ProjectiveLine S ↘ S).appTop.hom)
```

The new comparison is defined explicitly in
`lean/Sheaf/AlgebraicGeometry/ProjectiveLineDiagonalChernAdjunct.lean`.
It chooses no data and contains no postponed proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | The proof uses the factored comparison; its theorem statement is unchanged. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | G5 | Uses projection, chart and alpha; does not mention this trace. Source unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | Uses projection and chart; does not mention this trace. Source unchanged. |

## Status

landed 20261020T211622-L-3479464 2026-10-20 (merge of deliver/A7/Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals)
