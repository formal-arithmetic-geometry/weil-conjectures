# CategoryTheory.EvaluationDualityCompletion.Statement

## Reason

Restore the quarantined module and prove its theorem. The public mathematical definitions and
statement are preserved up to definitional equality. This record describes the proof-file options, private
helpers, local instance caches, and private proof imports so they can be reviewed.
No new public API or global instance is exported. No target definition changes.

## Old

```lean
def Statement : Prop :=
  let S := closed.{c, v, u, w} J R
  letI := S.monoidal
  ∀ (M : DerivedCategory (ringedSiteModules.{max c v u, max c v u, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))
    (h : ∀ N, IsIso (comparison S M N)),
    (λ_ M).inv ≫ coevaluation S M h ▷ M ≫ (α_ M (dual S M) M).hom ≫
        M ◁ S.evaluation M (𝟙_ _) ≫ (ρ_ M).hom = 𝟙 M ∧
    (ρ_ (dual S M)).inv ≫ dual S M ◁ coevaluation S M h ≫
        (α_ (dual S M) M (dual S M)).inv ≫ S.evaluation M (𝟙_ _) ▷ dual S M ≫
        (λ_ (dual S M)).hom = 𝟙 (dual S M) ∧
    Nonempty (tensorLeft M ⊣ tensorLeft (dual S M)) ∧
    Nonempty (tensorLeft (dual S M) ⊣ tensorLeft M) ∧
    (∀ (I : Type z), PreservesLimitsOfShape (Discrete I) (tensorLeft M)) ∧
    (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))
      (s : Cone F), Pretriangulated.IsHomotopyLimit s →
        Pretriangulated.IsHomotopyLimit ((tensorLeft M).mapCone s)) ∧
    ∀ [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))],
      ∃ L : AugmentedTowerCompletion.RoosLimit
          (A := ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)),
      ∀ X : ℕᵒᵖ ⥤ CommMon (ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)),
        Nonempty (AugmentedTowerCompletion.Model
          (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R))
          (AugmentedTowerCompletion.algebraComplexes X)
          (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit) ∧
        ∀ B : AugmentedTowerCompletion.Model
          (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R))
          (AugmentedTowerCompletion.algebraComplexes X)
          (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit,
        ∃ θ : B.completion ⋙ tensorLeft M ≅ tensorLeft M ⋙ B.completion,
          (∀ N, (tensorLeft M).map (B.unit.app N) ≫ θ.hom.app N =
            B.unit.app (M ⊗ N)) ∧
          (∀ N, IsIso (B.unit.app N) → IsIso (B.unit.app (M ⊗ N)))
```

The theorem evaluation_duality_completion had proof `by sorry`.

The quarantine archive retains the original public definitions and public imports.

## New

```lean
def Statement : Prop :=
  let S := closed.{c, v, u, w} J R
  letI := S.monoidal
  ∀ (M : DerivedCategory (ringedSiteModules.{max c v u, max c v u, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))
    (h : ∀ N, IsIso (comparison S M N)),
    let T := tensorLeft M
    (λ_ M).inv ≫ coevaluation S M h ▷ M ≫ (α_ M (dual S M) M).hom ≫
        M ◁ S.evaluation M (𝟙_ _) ≫ (ρ_ M).hom = 𝟙 M ∧
    (ρ_ (dual S M)).inv ≫ dual S M ◁ coevaluation S M h ≫
        (α_ (dual S M) M (dual S M)).inv ≫ S.evaluation M (𝟙_ _) ▷ dual S M ≫
        (λ_ (dual S M)).hom = 𝟙 (dual S M) ∧
    Nonempty (T ⊣ tensorLeft (dual S M)) ∧
    Nonempty (tensorLeft (dual S M) ⊣ T) ∧
    (∀ (I : Type z), PreservesLimitsOfShape (Discrete I) (T)) ∧
    (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))
      (s : Cone F), Pretriangulated.IsHomotopyLimit s →
        Pretriangulated.IsHomotopyLimit ((T).mapCone s)) ∧
    ∀ [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))],
      ∃ L : AugmentedTowerCompletion.RoosLimit
          (A := ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)),
      ∀ X : ℕᵒᵖ ⥤ CommMon (ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)),
        Nonempty (AugmentedTowerCompletion.Model
          (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R))
          (AugmentedTowerCompletion.algebraComplexes X)
          (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit) ∧
        ∀ B : AugmentedTowerCompletion.Model
          (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R))
          (AugmentedTowerCompletion.algebraComplexes X)
          (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit,
        ∃ θ : B.completion ⋙ T ≅ T ⋙ B.completion,
          (∀ N, (T).map (B.unit.app N) ≫ θ.hom.app N =
            B.unit.app (T.obj N)) ∧
          (∀ N, IsIso (B.unit.app N) → IsIso (B.unit.app (T.obj N)))

```

The theorem evaluation_duality_completion retains its original signature.

The theorem has a complete proof from its existing dependencies, with no new holes.
The added definitions and theorems are private. Local instance declarations provide
explicit ordinary module and cochain tensor structures, countable limits and colimits,
tensor preservation, and graded tensor instances at the independent coefficient universe.
The new instance caches are private and are declared after the public Statement.
All imported-instance registrations and irreducibility attributes are local.
The backward.isDefEq.respectTransparency options are scoped to this file's proof
elaboration. They change no imported declaration or target statement.
Private proof imports add the rigid-monoidal interchange lemma, native tensor exactness,
and KFlatAugmentedRoosComparison. The redundant separate fixed-tensor presentation
is omitted. Public imports and public mathematical signatures stay as in the archive.
The Statement predicate now shares tensorLeft M through a local let T := tensorLeft M,
and uses T.obj N for the definitionally identical M tensor N. This prevents repeated
elaboration of the same localization tensor and preserves the proposition by zeta
reduction. No extra hypothesis, object, or conclusion is introduced. The closed
structure is locally irreducible only during this proof.
Explicit universe parameters on the existing K-flat predicate merely pin the universe
already determined by R and the complex's module category.

## Users

The item is absent from the current live Lean tree and restored from its rework archive.
The read-only downstream.py inventory reports “unknown module”; direct import and name
searches in both live roots and quarantine find no other current Lean consumer.
Its unfinished DAG parent is retained, so it is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.EvaluationDualityCompletion | G2 | Restored; private helpers and complete proof. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | DAG parent retained; no public interface change or source adaptation. |

## Status

landed 20261024T014839-L-2284170 2026-10-24 (merge of deliver/G2/Sheaf.SixFunctors.EvaluationDualityCompletion)
