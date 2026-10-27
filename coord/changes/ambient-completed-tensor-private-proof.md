# CategoryTheory.AmbientCompletedTensor.ambientCompletedTensorAdjunction

## Reason

Complete three of the four existing theorem proofs; retain the original general adjunction hole. The proof uses private scalar-extension,
strict-sequence, unit-transport and principal-cone helpers. Additional opens, universes,
private proof imports, a private additive instance and file-local reducibility attributes
support those proofs. The imported generic essentially-small sheafification instance is
removed from instance search in this module so that explicit coefficient-universe
instances are used; the change is private to the module system. Existing public imports,
public declaration signatures and data definition bodies stay unchanged. No target meaning
changes and no consumer needs adaptation.

## Old

The four theorem bodies were `by sorry`:

- `CategoryTheory.AmbientCompletedTensor.finiteTensorStep_existsUnique`
- `CategoryTheory.AmbientCompletedTensor.ambientCompletedTensorAdjunction`
- `WeilConjectures.integralAmbientCompletedTensorAdjunction`
- `WeilConjectures.integralConstructible_locallyComplete`

The original signatures (retained verbatim) are:

```lean
theorem finiteTensorStep_existsUnique (n : ℕ) :
    ∃! t : finiteTensor J A I (n + 1) ⟶ finiteTensor J A I n,
      ∀ (P Q : Cx (completed J A I)) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (a b : (finite J A I (n + 1)).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((t.app (P, Q)).f k).val.app U
            (finiteGenerator J A I (n + 1) P Q p q k h U a b x y) =
          finiteGenerator J A I n P Q p q k h U
            ((transition J A I n).hom.app U a) ((transition J A I n).hom.app U b) x y

theorem ambientCompletedTensorAdjunction [IsNoetherianRing A]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (S : CoefficientClosedStructure
      (@derivedInternalHomOfUniverses.{u, u, u, u + 1} C _ J _ _ (completed J A I)
        (HasDerivedCategory.standard _)))
    (models : @CoefficientTensorModels.{u, u, u, u + 1} C _ J _ _ (completed J A I)
      (HasDerivedCategory.standard _) S) :
    ∃ (T : D (completed J A I) × D (completed J A I) ⥤ TD (completed J A I))
      (β : S.tensor ⋙ (quotientPresentation J A I true).tower ≅ T)
      (ν : S.tensor ⟶ T ⋙ rlim (completed J A I)),
      (∀ (P Q : (Good J A I).FullSubcategory),
        ∃ (V : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ)
          (κ : V.asFunctor ≅ (finiteTensorTower J A I).obj (P.obj, Q.obj))
          (e : T.obj ((goodLocalization J A I).obj P,
            (goodLocalization J A I).obj Q) ≅ (TQ (completed J A I)).obj V)
          (b : reductionComplex J A I true
            ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P.obj, Q.obj)) ≅ V),
          β.hom.app ((goodLocalization J A I).obj P, (goodLocalization J A I).obj Q) ≫
              e.hom =
            (quotientPresentation J A I true).tower.map
                (models.iso J (completed J A I) S P.obj Q.obj
                  P.property.1 Q.property.1).inv ≫
              (quotientPresentation J A I true).comparison.app
                ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P.obj, Q.obj)) ≫
              (TQ (completed J A I)).map b.hom ∧
          ∀ (n : ℕ) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
            (c : (finite J A I n).obj.obj U)
            (x : (P.obj.X p).val.obj U) (y : (Q.obj.X q).val.obj U),
            ((κ.hom.app (op n)).f k).val.app U
                (((b.hom.f k).app (op n)).val.app U
                  (tensorSection (projection J A I n)
                    (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj
                      (P.obj, Q.obj)).X k) U c
                    (coefficientTensorGenerator.{u, u, u} J (completed J A I)
                      P.obj Q.obj p q k h U x y))) =
              finiteGenerator J A I n P.obj Q.obj p q k h U 1 c x y) ∧
      (∀ M : D (completed J A I) × D (completed J A I),
        (completionUnit J A I true).app (S.tensor.obj M) ≫
          (rlim (completed J A I)).map (β.hom.app M) = ν.app M) ∧
      (∃ (K : KoszulPresentation J A I true r a)
        (γ : T ⋙ rlim (completed J A I) ≅ S.tensor ⋙ koszulCompletion J A I K),
        ∀ M : D (completed J A I) × D (completed J A I),
          ν.app M ≫ γ.hom.app M = koszulUnit J A I K (S.tensor.obj M)) ∧
      (∀ (M : D (completed J A I) × D (completed J A I)) (L : D (completed J A I)),
        IsComplete (projection J A I 0) L →
          Function.Bijective (fun f : (T ⋙ rlim (completed J A I)).obj M ⟶ L ↦
            ν.app M ≫ f))

theorem integralAmbientCompletedTensorAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) :
    ∀ (P L K : IntegralOnSlice.D.{t, u} l E X none),
      (∀ (U : X.ProEt)
        (s : ((IntegralOnSlice.ring.{t, u} l E X (some U)).obj ⋙
            forget CommRingCat.{max u (t + 1)}).sections),
        (∃ Z : Sieve U, Z ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
          ∀ (V : X.ProEt) (f : V ⟶ U), Z f →
            ∃ c : (completedIntegralCoefficientSheafUnrestricted.{t, u} l E X).obj.obj (op V),
              s.val (op (Over.mk f)) = integralCompletionScalarValue.{t, u} l E X (op V) * c) →
        IsZero (integralCompletionLocalTest.{t, u} l E X K U s)) →
      Function.Bijective (fun f :
        (IntegralOnSlice.completedTensor.{t, u} l E X none).obj (P, L) ⟶ K ↦
        (IntegralOnSlice.completionUnit.{t, u} l E X none).app
          ((@RingedSiteDualityModel.closed.{t + 1, t, u, (max u (t + 1)) + 1}
            _ _ _ (IntegralOnSlice.abSheafify.{t, u} X none)
            (IntegralOnSlice.abLocallyBijective.{t, u} X none) _ _
            (IntegralOnSlice.duality.{t, u} l E X none)).tensor.obj (P, L)) ≫ f)

theorem integralConstructible_locallyComplete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u}) :
    ∀ K : IntegralOnSlice.D.{u, u} l E X none,
      sfIntegralConstructible.{u} l E X K →
        ∀ (U : X.ProEt)
          (s : ((IntegralOnSlice.ring.{u, u} l E X (some U)).obj ⋙
            forget CommRingCat.{u + 1}).sections),
          (∃ Z : Sieve U, Z ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
            ∀ (V : X.ProEt) (f : V ⟶ U), Z f →
              ∃ c : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj (op V),
                s.val (op (Over.mk f)) = integralCompletionScalarValue.{u, u} l E X (op V) * c) →
          IsZero (integralCompletionLocalTest.{u, u} l E X K U s)
```

## New

The finite transition and both integral signatures have complete proofs from existing library
declarations. The general ambient adjunction retains its original sorry.
All additional helpers are private and proved. All added imports are private proof imports.
Reducibility attributes are local. As in the existing principal-cone comparison module,
unused-variable and unused-section-variable linting is disabled for the dependent
transport proofs, avoiding expansion of large tensor constructions during relevance
checks; the kernel still checks every proof. The final file has no profiler settings. The additional additive instance applies only
to the private reduction proof machinery. No new public declarations or modules are introduced.
The strict balanced maps have their explicit generator equations; no arbitrary witness is
used as a new mathematical object. The unchanged public finiteTensorStep remains chosen
from its uniquely specified transition theorem.

## Users

Read-only `tools/downstream.py Sheaf.Paper.AmbientCompletedTensorAdjunction` reports one
consumer. The declarations and importer-visible interface are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientCompletedTensorAdjunction | Q1 | Three theorem proofs and private helpers; one original hole retained. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | unclaimed | No adaptation. |

## Status

landed 20261025T095732-L-3474102 2026-10-25 (merge of deliver/Q1/Sheaf.Paper.AmbientCompletedTensorAdjunction)
