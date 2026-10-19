# CompactSupportFiniteCoefficientComparison withdrawal

## Reason

The comparison module has one direct importer and one external consumer of each of its
public declarations: `WeilConjectures.WeilSheaf.Finiteness`. That consumer only needs the
constant-coefficient compact-support vanishing bound, not an injection into the scalar
extension of a product. Replace its proof using dense proper compactification, the existing
ordinary finite-coefficient bound, proper coincidence and localization. The closed complement
has strictly smaller dimension, so its preceding cohomology vanishes too. This withdraws the
unused stronger comparison under worker brief step 8d.

Finiteness is unclaimed. Its existing signatures, definitions and public imports are identical.
Only proof imports, proved private helpers and the upper-bound proof change.
The redundant private imports of LowerStarPairing, FieldBaseChangeDimension and
Etale.Derived.Finiteness.CohomologicalDimension are removed; all public imports stay identical. No target type or
definition used by a target changes. The definitions in the withdrawn module were used solely
in this proof, which is adapted in the same delivery. No arbitrary lattice or witness is chosen.

## Old

The following declarations of the withdrawn module are removed, with their surrounding
variables unchanged:

```lean
noncomputable def finiteLevelCompactSupportSections (n : ℕ) (r : ℤ) :
    ModuleCat.{u + 1} (PadicInt l) :=
  let Λ := ULift.{u + 1} (ZMod (l ^ (n + 1)))
  let f := (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  haveI : HasCompactification f := by
    dsimp only [f, Scheme.Hom.geometricFiberToAlgebraicClosure]
    infer_instance
  let ρ : PadicInt l →+* Λ :=
    ULift.ringEquiv.symm.toRingHom.comp (PadicInt.toZModPow (n + 1))
  (ModuleCat.restrictScalars ρ).obj
    ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
      ((DerivedCategory.homologyFunctor _ r).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)))))

/-- Constant adic compactly supported cohomology embeds into the scalar extension of the
product of its finite-coefficient groups. There is no dimension or degree restriction.

Source: Bhatt--Scholze, Lemmas 6.1.13, 6.5.8--6.5.9, 6.7.7, Proposition 6.8.14,
and Remark 6.8.15;
Milne, Lectures on Etale Cohomology, §18 and Theorems 19.1--19.2.
(blueprint: lem-pod-compact-support-finite-coefficient-comparison).

Proof: Use the canonical refinement comparisons to work with the same compactification
of the geometric structure morphism at every coefficient stage. Put
`C = RΓ(bar X, j_! ℤ_ℓ)` on the pro-etale site. Here `j_!` commutes with homotopy
limits (Lemma 6.1.13) and preserves constructibility (Lemma 6.5.8), so the constant lattice
and its extension by zero are derived complete. The finite-level comparison identifies `C`
with `R lim_n RΓ(bar X_et, j_! ℤ/ℓ^(n+1))`. The groups at every finite
level are finite, by constructible torsion finiteness on the proper compactification.
Consequently their inverse systems are Mittag--Leffler: the images in each finite group
stabilize. The Milnor exact sequence has zero `lim¹` term, giving
`H^r(C) ≅ lim_n H_c^r(X ⊗ k̄, ℤ/ℓ^(n+1))` as `ℤ_ℓ`-modules. The limit is a submodule of the
product appearing here. Coefficient extension identifies the source with
`ℚ̄_ℓ ⊗[ℤ_ℓ] H^r(C)`: first invert `ℓ`, then extend the field, using the constant integral
lattice. Both extensions are flat, so tensoring the inclusion of the limit into the product
is injective. Compose it with this coefficient comparison. Forgetting the Weil structure
identifies the source with the ordinary constant adic cohomology used in this calculation;
no Frobenius compatibility of the embedding is required. The empty scheme and negative
degrees give zero groups on both sides by the same construction. -/
theorem exists_injective_compactSupportFiniteCoefficientComparison (r : ℤ) :
    ∃ f : ((adicConstant k₀ l X).compactlySupportedCohomology r).carrier →ₗ[PadicAlgCl l]
        PadicAlgCl l ⊗[PadicInt l]
          (∀ n, finiteLevelCompactSupportSections (k₀ := k₀) l X n r),
      Function.Injective f := by sorry

```

## New

The module is withdrawn via `deleted.txt` and lands as an empty `module` file. No replacement
comparison theorem is introduced. The existing declaration
`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant` retains
its exact signature:

```lean
theorem subsingleton_compactlySupportedCohomology_adicConstant (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (r : ℤ) (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).compactlySupportedCohomology r).carrier
```

Its upper-bound proof now uses a dense compactification `X -> Y`, its closed boundary `Z`,
the constant-adic ordinary bound on both proper schemes and the exact localization sequence.
For `r > 2e` and nonempty boundary of dimension `z < e`, both `H_c^r(Y)` and `H_c^(r-1)(Z)`
vanish. The empty boundary is treated directly. The induced injection from the long exact
sequence gives the unchanged conclusion. All newly added helpers are private and proved. The helpers are
unitOrdinaryBound, forgetConstantIso, pullbackConstantIso,
subsingleton_cohomology_of_forget_homology_isZero, properUnitVanishing and
properEmptyVanishing (six declarations: four theorems and two explicit isomorphisms).

## Users

Read-only `tools/downstream.py` reports 101 downstream modules and only Finiteness as an
external textual consumer. Repeating it for `finiteLevelCompactSupportSections` has the same
sole external consumer. The direct import search has the same result.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| TargetsCheck | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.Statement | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Proof replaced, signature and public imports unchanged; sole direct consumer adapted. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Indirect user; same visible declarations and statement meanings; no adaptation. |

## Status

landed 20261019T112624-L-3962618 2026-10-19 (merge of deliver/Y5/Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison)
