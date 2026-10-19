# WeilConjectures.properCompactCoincidence

## Reason

Complete the proper-coincidence proof using private identity-open, finite-clopen,
compactification-change and ordinary-Roos-value helpers. Preflight classifies the
added file-local elaboration options as changed visible commands and requires this
record. No existing signature, instance body, public import or definition changes.
The protected unit-route import `Sheaf.Paper.CompactificationCoherence` is retained.

## Old

The original file uses the following elaboration context:

```lean
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)
```

The original theorem signature, verbatim:

```lean
theorem properCompactCoincidence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
        n hn Y).ι ⋙ @sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
          (Y ↘ Spec (CommRingCat.of D.k)) c
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)
          _ (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn) ≅
      (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn Y).ι ⋙
        proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)) ∧
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ⋙
          (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) Y).ι ⋙
        sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E₀) (Y ↘ Spec (.of D.k))) ∧
    Nonempty (sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ≅
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper (Y ↘ Spec (.of D.k))) (Coefficient.{u} l Ω E₀)) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      ∀ S₀ : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
          (Compactification.ofIsProper (Y ↘ Spec (.of D.k))),
        Nonempty (S.system.functor ≅ S₀.system.functor)) ∧
    (∀ K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
        Y).FullSubcategory,
      Nonempty (finiteCompactSections D l (Coefficient.{u} l Ω E₀) Y c n hn K.obj ≅
        finiteOrdinarySections D l (Coefficient.{u} l Ω E₀) Y n hn K.obj) ∧
      ∀ i : ℤ, Nonempty (finiteCompactCohomology D l
        (Coefficient.{u} l Ω E₀) Y c n hn K.obj i ≅
          finiteOrdinaryCohomology D l (Coefficient.{u} l Ω E₀) Y n hn K.obj i)) ∧
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K ≅
          integralImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (integralCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        integralOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (integralCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ integralOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfRationalCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K.obj ≅
          rationalImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (rationalCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        rationalOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (rationalCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ rationalOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      Nonempty (sfQbarCompactSupportValue l D.k (finiteFieldDatumPrimeUnit D l hl)
        Ω c K.stage K.obj.obj ≅ qbarImage D l hl Y Ω K) ∧
      Nonempty (qbarCompactSections D l hl Y Ω c K ≅ qbarOrdinarySections D l hl Y Ω K) ∧
      ∀ i : ℤ, Nonempty (qbarCompactCohomology D l hl Y Ω c K i ≅
        qbarOrdinaryCohomology D l hl Y Ω K i))
```

Its proof was `by sorry`. The point Over instance is unchanged.

## New

The identical theorem signature is retained verbatim:

```lean
theorem properCompactCoincidence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
        n hn Y).ι ⋙ @sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
          (Y ↘ Spec (CommRingCat.of D.k)) c
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)
          _ (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn) ≅
      (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn Y).ι ⋙
        proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)) ∧
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ⋙
          (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) Y).ι ⋙
        sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E₀) (Y ↘ Spec (.of D.k))) ∧
    Nonempty (sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ≅
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper (Y ↘ Spec (.of D.k))) (Coefficient.{u} l Ω E₀)) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      ∀ S₀ : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
          (Compactification.ofIsProper (Y ↘ Spec (.of D.k))),
        Nonempty (S.system.functor ≅ S₀.system.functor)) ∧
    (∀ K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
        Y).FullSubcategory,
      Nonempty (finiteCompactSections D l (Coefficient.{u} l Ω E₀) Y c n hn K.obj ≅
        finiteOrdinarySections D l (Coefficient.{u} l Ω E₀) Y n hn K.obj) ∧
      ∀ i : ℤ, Nonempty (finiteCompactCohomology D l
        (Coefficient.{u} l Ω E₀) Y c n hn K.obj i ≅
          finiteOrdinaryCohomology D l (Coefficient.{u} l Ω E₀) Y n hn K.obj i)) ∧
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K ≅
          integralImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (integralCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        integralOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (integralCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ integralOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfRationalCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K.obj ≅
          rationalImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (rationalCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        rationalOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (rationalCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ rationalOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      Nonempty (sfQbarCompactSupportValue l D.k (finiteFieldDatumPrimeUnit D l hl)
        Ω c K.stage K.obj.obj ≅ qbarImage D l hl Y Ω K) ∧
      Nonempty (qbarCompactSections D l hl Y Ω c K ≅ qbarOrdinarySections D l hl Y Ω K) ∧
      ∀ i : ℤ, Nonempty (qbarCompactCohomology D l hl Y Ω c K i ≅
        qbarOrdinaryCohomology D l hl Y Ω K i))
```

The file additionally uses these elaboration options in its existing section:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

They support the published derived-functor interfaces during elaboration of this
file; importing modules do not inherit these options. Every new helper is private
and fully proved. The proof-only imports added are:

- `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper`
- `Sheaf.Paper.FiniteDirectImageComposition`
- `Sheaf.Paper.FieldShriekCompositionQcqs`
- `Sheaf.Paper.CompactSupportFiniteFieldIndependence`
- `Sheaf.Paper.SystemOperationExchangeRealization`

The eight unused private imports removed are listed in report.md. All existing
public imports are preserved. The owning DAG node's proof, proof dependencies and
proof origin describe the actual proof. The original theorem docstring records its
source proof plan; the node and report explain the shorter implementation.
No target type or definition used in a target changes its meaning.

## Users

The source scan has one direct importer,
`Sheaf.Paper.ProperCoincidenceFrobenius` (held by T6). No source adaptation is
needed: the complete existing public API, point instance and public imports are
unchanged. The new private helper declarations do not occur in public signatures.
The completed `tools/downstream.py --uses` scan lists 35 downstream modules;
neither existing declaration is mentioned by name in any downstream source.
The table includes all 35 transitive consumers. They see the same public API;
none is adapted in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ProperCompactCoincidence | P9 | Same signature, completed proof; no new holes. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | Same public API; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same public API; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | Same public API; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | Same public API; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Same public API; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same public API; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same public API; no adaptation. |
| TargetsCheck | unclaimed | Same public API; no adaptation. |
| WeilConjectures | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same public API; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same public API; no adaptation. |

## Status

landed 20261019T231306-L-570278 2026-10-19 (merge of deliver/P9/Sheaf.Paper.ProperCompactCoincidence)
