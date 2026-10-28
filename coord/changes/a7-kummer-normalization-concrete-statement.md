# AlgebraicGeometry.ProEtale.strict_kummer_pure_kernel_normalization

## Reason

A profiled check of the statement with a sorry body spends 35.9 seconds in kernel
type checking, before any proof is checked. Name the exact concrete conclusion
as strictKummerPureKernelNormalizationStatement in its own module. Its actual coefficient record fields are the former explicit parameters.
Expanding this record and Normalized gives the old conclusion by definitional equality. Only the printed conclusion
changes; all binders, universes, hypotheses and mathematical content are identical.
The five Challenge declarations and the generic normalization definition are
unchanged. The named proposition is not marked irreducible, so consumers may
continue to use the theorem at its former conclusion by definitional equality.

## Old

```lean
theorem strict_kummer_pure_kernel_normalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
  KummerPureKernelNormalization
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W)
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    (fun n => kummerComparedUnit ℓ W hW n)
    (kummerRootNormalization ℓ W hW)
    (fun n ↦ diagonalFiniteForgetIso ℓ n W) η
```

## New

```lean
theorem strict_kummer_pure_kernel_normalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
  strictKummerPureKernelNormalizationStatement ℓ W hW D η
```

The real coefficient record and named proposition are:

```lean
def strictKummerNormalizationCoefficients (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) :
    KummerNormalizationCoefficients (hA := kummerAbHasExt W) (diagonalForget ℓ W)
      (fun n ↦ Sheaf (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))) where
  catC := fun n ↦ inferInstance
  TateF := fun n ↦ diagonalFiniteToPadic ℓ n W
  V := fun n ↦ cartierForget (diagonalResidue.{u} ℓ n) W
  M := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf
  R := Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)
  P := fun n ↦ geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
    (cartierResidue_cast ℓ (n + 1)) W
  κ := fun n ↦ kummerComparedUnit ℓ W hW n
  rootNorm := kummerRootNormalization ℓ W hW
  σ := fun n ↦ diagonalFiniteForgetIso ℓ n W
  rootMap := fun n ↦ cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
    (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
    (by simpa using hW.pow (n + 1))

/-- The exact concrete specialization of KummerPureKernelNormalization, using
shared coefficients. Expanding the two real definitions gives the old concrete
conclusion. No hypothesis or conclusion changes and no data is chosen.
Source: diagonal tower proof, steps (3) and (4)
(blueprint: def-sfb-kummer-pure-kernel-normalization-statement). -/
def strictKummerPureKernelNormalizationStatement (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) : Prop :=
  (strictKummerNormalizationCoefficients ℓ W hW).Normalized
    ℓ (diagonalScalarExtension ℓ W) (diagonalScalarAdjunction ℓ W) D η
```

The generic Normalized definition is precisely the unchanged
KummerPureKernelNormalization applied to the record fields. Profiling the first
uncached specialization still exceeded the limit; this explicit record shares
those parameters in the abstract application and removes repeated checks of
the same concrete category structures.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictKummerUnitNormalization | unclaimed | Compiled unchanged against the definitionally identical conclusion. |

All DAG citers preserve their uses: only the Lean spelling of the unchanged
proposition changes. The existing node statement is unchanged; its lean record
and the new definition dependency are updated.

## Status

landed 20261028T020145-L-2471939 2026-10-28 (merge of deliver/A7/Sheaf.Paper.StrictKummerPureKernelNormalization)
