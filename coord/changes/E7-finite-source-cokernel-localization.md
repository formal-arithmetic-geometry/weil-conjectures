# Module.finiteProjectiveCokernel_residue_localization

## Reason

The affine cut applies the residue criterion to im(d0) -> K1. The source is finite,
but need not be projective before localization. The existing proof already establishes
the stronger result with a finite source: its local splitting criterion assumes only
finiteness of the source; clearing denominators uses finite presentation of the target
and finiteness of the source. Drop the unused source-projectivity binder. This is a
stronger theorem, retaining both original conclusions, not a weakening of the affine cut.
The dependency module was unclaimed when edited. No definitions or targets change.
The zero-source and zero-target cases are covered by the same splitting criterion;
there is no nonzero-rank assumption.

## Old

```lean
theorem finiteProjectiveCokernel_residue_localization
    {R : Type u} [CommRing R]
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
    [Module.Projective R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂]
    [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (φ.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f))) ∧
        Module.Projective (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (φ.baseChange (Localization.Away f)))
```

## New

```lean
theorem finiteProjectiveCokernel_residue_localization
    {R : Type u} [CommRing R]
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂]
    [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (φ.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f))) ∧
        Module.Projective (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (φ.baseChange (Localization.Away f)))
```

## Users

All 29 transitive downstream modules from tools/downstream.py were checked for direct
uses and semantic impact. The only existing direct application is in
ResidueBottomDifferential, and it supplies the map and prime without explicit instance
arguments. No consumer signature or definition changes. The original direct consumer compiles,
but now reports `Variable name hp₀ is not explicitly referenced`, because the strengthened
lemma no longer consumes that hypothesis implicitly. The unclaimed
ResidueBottomDifferential receives one explicit local instance binding to `hp₀` at the
start of its proof, preserving its complete signature and fixing this new warning.
There are no adaptations of modules held by another group.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero | E7 | New proof uses the strengthened lemma for the finite image of d0; signature unchanged. |
| Sheaf.Algebra.Homology.ResidueBottomDifferential | unclaimed | Only other direct application; one explicit local instance from hp₀ prevents the newly unused-variable warning; signature unchanged. |
| Sheaf.Algebra.Homology.ResidueConnectiveProjectiveOpcycles | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.Algebra.Homology.UniversalConnectiveProjectiveModel | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.Algebra.Homology.UniversalH0ProjectiveNormalization | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | H5 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | U2 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | M3 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | C6 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | D9 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero | C9 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | Z5 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | R5 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | T8 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | X5 | No direct use of the declaration; imports and all statements/definitions unchanged. |
| Sheaf.RingTheory.FiniteProjectiveCokernelLocalization | unclaimed | Remove unused source-projectivity binder; proof unchanged; module unclaimed. |

## Status

landed 20261018T062738-L-645175 2026-10-18 (merge of deliver/E7/Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero)
