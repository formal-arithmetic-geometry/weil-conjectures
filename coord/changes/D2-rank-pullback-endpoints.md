# AlgebraicGeometry.ProEtale.exists_clopen_rank_decomposition_of_isLisse

## Reason

Make inferred source and target arguments explicit on three coefficient pullback expressions. The old inference retained identity-functor and constant-functor object wrappers; conversion against a finite-free module on the underlying scheme caused kernel timeouts. All mathematical hypotheses and conclusions are identical, with no binder or universe change.

Repair of returned head `1ec7410dd5d` (reviewer C-1ec74): the proof passed review,
but landing rejected the reviewer's flat fix filename. This complete record is included
at `coord/changes/D2-rank-pullback-endpoints.md` in the delivery. The stage-3 landing API
expects a reviewer override of this record to be named
`D2-rank-pullback-endpoints.change.md`; the rejected filename lacked `.change`.
No override of this record is requested. The delivery tool rebuilds the packet on current
`sheaf-dag`; no launcher or landing tools are changed.

## Old

```lean
theorem exists_clopen_rank_decomposition_of_isLisse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (@Profinite.continuousCoefficientRingObj E
        (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
        (@NonUnitalSeminormedRing.toIsTopologicalRing E
          (@SeminormedRing.toNonUnitalSeminormedRing E
            (spectralNorm.seminormedRing ℚ_[l] E)))) X))
    (hL : IsLisseCoefficientModule (@Profinite.continuousCoefficientRingObj E
      (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
      (@NonUnitalSeminormedRing.toIsTopologicalRing E
        (@SeminormedRing.toNonUnitalSeminormedRing E
          (spectralNorm.seminormedRing ℚ_[l] E)))) L) :
    ∃ R : ℕ → X.Opens,
      (∀ r : ℕ, IsClosed (R r : Set X)) ∧
      (∀ (x : X) (r : ℕ), x ∈ R r ↔
        ∃ (U : X.ProEt) (v : U.left), U.hom v = x ∧
          Nonempty
            ((CondensedRing.upperStar (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) r)) ∧
      (∀ (U : X.ProEt) (n : ℕ),
        Nonempty
          ((CondensedRing.upperStar (@Profinite.continuousCoefficientRingObj E
            (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
            (@NonUnitalSeminormedRing.toIsTopologicalRing E
              (@SeminormedRing.toNonUnitalSeminormedRing E
                (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
            Mod.finiteFree
              (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                (@NonUnitalSeminormedRing.toIsTopologicalRing E
                  (@SeminormedRing.toNonUnitalSeminormedRing E
                    (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) n) →
        ∀ (v : U.left) (r : ℕ), U.hom v ∈ R r ↔ n = r) ∧
      (CompactSpace X → {r : ℕ | (R r : Set X).Nonempty}.Finite) ∧
      IsIso (Sigma.desc (fun r : ℕ ↦ (R r).ι)) ∧
      ∀ r : ℕ, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (R r).toScheme,
        ∀ i : C.I₀,
          Nonempty
            ((CondensedRing.upperStar (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E))))
                (C.f i ≫ (R r).ι)).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) (C.X i)) r) 
```

## New

```lean
theorem exists_clopen_rank_decomposition_of_isLisse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (@Profinite.continuousCoefficientRingObj E
        (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
        (@NonUnitalSeminormedRing.toIsTopologicalRing E
          (@SeminormedRing.toNonUnitalSeminormedRing E
            (spectralNorm.seminormedRing ℚ_[l] E)))) X))
    (hL : IsLisseCoefficientModule (@Profinite.continuousCoefficientRingObj E
      (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
      (@NonUnitalSeminormedRing.toIsTopologicalRing E
        (@SeminormedRing.toNonUnitalSeminormedRing E
          (spectralNorm.seminormedRing ℚ_[l] E)))) L) :
    ∃ R : ℕ → X.Opens,
      (∀ r : ℕ, IsClosed (R r : Set X)) ∧
      (∀ (x : X) (r : ℕ), x ∈ R r ↔
        ∃ (U : X.ProEt) (v : U.left), U.hom v = x ∧
          Nonempty
            ((CondensedRing.upperStar (X := U.left) (Y := X)
              (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) r)) ∧
      (∀ (U : X.ProEt) (n : ℕ),
        Nonempty
          ((CondensedRing.upperStar (X := U.left) (Y := X)
              (@Profinite.continuousCoefficientRingObj E
            (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
            (@NonUnitalSeminormedRing.toIsTopologicalRing E
              (@SeminormedRing.toNonUnitalSeminormedRing E
                (spectralNorm.seminormedRing ℚ_[l] E)))) U.hom).obj L ≅
            Mod.finiteFree
              (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                (@NonUnitalSeminormedRing.toIsTopologicalRing E
                  (@SeminormedRing.toNonUnitalSeminormedRing E
                    (spectralNorm.seminormedRing ℚ_[l] E)))) U.left) n) →
        ∀ (v : U.left) (r : ℕ), U.hom v ∈ R r ↔ n = r) ∧
      (CompactSpace X → {r : ℕ | (R r : Set X).Nonempty}.Finite) ∧
      IsIso (Sigma.desc (fun r : ℕ ↦ (R r).ι)) ∧
      ∀ r : ℕ, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (R r).toScheme,
        ∀ i : C.I₀,
          Nonempty
            ((CondensedRing.upperStar (X := C.X i) (Y := X)
              (@Profinite.continuousCoefficientRingObj E
              (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
              (@NonUnitalSeminormedRing.toIsTopologicalRing E
                (@SeminormedRing.toNonUnitalSeminormedRing E
                  (spectralNorm.seminormedRing ℚ_[l] E))))
                (C.f i ≫ (R r).ι)).obj L ≅
              Mod.finiteFree
                (condensedRingObj (@Profinite.continuousCoefficientRingObj E
                  (spectralNorm.normedField ℚ_[l] E).toUniformSpace.toTopologicalSpace _
                  (@NonUnitalSeminormedRing.toIsTopologicalRing E
                    (@SeminormedRing.toNonUnitalSeminormedRing E
                      (spectralNorm.seminormedRing ℚ_[l] E)))) (C.X i)) r) 
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StratifiedLatticeRank | D2 | Proof completed; endpoint annotations only. |

The declaration has no external textual users according to tools/downstream.py --uses. The three direct importing modules Sheaf.Paper.DlConstructibleFibresExact, Sheaf.Paper.PerAdicNormalizedFibreComparisons and Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators do not call it; the exported mathematical proposition is definitionally unchanged (the old statement inferred the endpoints `(𝟭 Scheme).obj U.left` and `(Functor.fromPUnit X).obj U.right`, which reduce to `U.left` and `X`; the third clause already had `C.X i` and `X`) and no adaptations are required.

## Status

landed 20261021T233630-L-840632 2026-10-21 (merge of deliver/D2/Sheaf.Paper.StratifiedLatticeRank)
