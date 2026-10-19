# AlgebraicGeometry.ProEtale.reductionDirectImage_cocycle and reductionDirectImage_isIso

## Reason

Complete the coefficient cocycle and formalize the isomorphism reduction, including
all six intrinsic membership claims, using private helpers and new factor lemmas.
The static preflight flags the new namespace boundary, declaration-scoped options, and
local irreducibility attributes as a possible interface change. The attributes are
local: they affect proof elaboration only. All existing signatures, definitions and
public imports remain unchanged; the new item imports are proof-only.

## Old

```lean
theorem reductionDirectImage_cocycle
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((reductionCompactSupport A j p).obj M) ≫
      (reductionDirectImageComparison (ψ.comp φ) j p).app M =
    (scalarExtensionFunctor ψ Y).map ((reductionDirectImageComparison φ j p).app M) ≫
      (reductionDirectImageComparison ψ j p).app ((scalarExtensionFunctor φ X).obj M) ≫
        (reductionCompactSupport C j p).map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M) := by
  sorry
```

The other replaced proof has the following unchanged signature:

```lean
theorem reductionDirectImage_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    IsIso ((reductionDirectImageComparison φ j p).app M) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)) := by
  sorry
```

## New

```lean
theorem reductionDirectImage_cocycle
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((reductionCompactSupport A j p).obj M) ≫
      (reductionDirectImageComparison (ψ.comp φ) j p).app M =
    (scalarExtensionFunctor ψ Y).map ((reductionDirectImageComparison φ j p).app M) ≫
      (reductionDirectImageComparison ψ j p).app ((scalarExtensionFunctor φ X).obj M) ≫
        (reductionCompactSupport C j p).map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M)
```

The second signature is also unchanged:

```lean
theorem reductionDirectImage_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    IsIso ((reductionDirectImageComparison φ j p).app M) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M))
```

Its proof constructs etale origins, proves both actual lower bounds, applies
properIntrinsicFiniteCoefficientExtension, and proves all six membership claims with
compactSupport_uniform_tor_bound and scalar preservation.

The cocycle statement is proved by compactSupport_cocycle_of_factors from
proved proper and open coefficient cocycles. The private helper and local proof
context do not occur in any public signature or definition.

## Users

No existing statement or definition changes, so no downstream adaptation is required.
The downstream command reports 211 transitive importers. The only textual occurrence
of reductionDirectImage_cocycle is its own declaration; all 211 importers retain the
identical existing interface. No module held by another group is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Two proof bodies and private proof context. |

## Status

landed 20261019T192718-L-1858129 2026-10-19 (merge of deliver/F1/Sheaf.SecSmoothPurity.ReductionDirectImage)
