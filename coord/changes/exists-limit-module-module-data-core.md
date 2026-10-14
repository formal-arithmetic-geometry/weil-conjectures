# exists_limit_module_module_data_core

## Reason

Repair of X-d42bc: the corrected joint core and wrapper duplicated the existing
RingHom.exists_limit_module_essentially_finite_presentation_over_system statement.
Retire both false original supplied-diagram interfaces instead of replacing them by
copies of the joint theorem. Put the real ring/module assembly into the existing
joint theorem, preserving its exact signature and visibility. Its original proof
necessarily fails after the wrapper is removed.

## Old

### Old core (verbatim signature from the delivery base)

```lean
theorem exists_limit_module_module_data_core
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (N : AddCommGrpCat.{max u v}) [Module T N] (s t : ℕ)
    (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N))
    {i₀ : I} {B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}}
    {β : B ⟶ (Functor.const _).obj T}
    (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T)
    (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i)
    (hκ : ∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x)
    (hτ : ∀ i, IsLocalHom (τ₀ i))
    (hτe : ∀ i, (τ₀ i).EssFiniteType)
    (hcomp : ∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom)
    (hnat : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      (B.map (homOfLE h)).hom.comp (τ₀ i) = (τ₀ j).comp (F.map (homOfLE h)).hom)
    (D : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{max u v})
    (δ : D ⟶ (Functor.const _).obj N)
    (hD : Nonempty (IsColimit (Cocone.mk N δ))) :
      ∃ (ν : ∀ i : {i : I // i₀ ≤ i}, D.obj i →+ N)
        (_ : ∀ i : {i : I // i₀ ≤ i}, Module (B.obj i) (D.obj i)),
        (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
        (∀ i, ∀ (y : B.obj i) (x : D.obj i), ν i (y • x) = κ i y • ν i x) ∧
        (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j)
          (y : B.obj i) (x : D.obj i),
          (D.map (homOfLE h)).hom (y • x) =
            (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
        (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
        (∀ i, ∃ H₀ : (Fin s → B.obj i) →ₗ[B.obj i] (Fin t → B.obj i),
          Nonempty (((Fin t → B.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B.obj i] D.obj i)) ∧
        (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
          letI := (τ₀ i).toAlgebra
          letI := (F.map (homOfLE h)).hom.toAlgebra
          (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
            (∀ (x : B.obj i) (y : F.obj j.1),
              φ (x ⊗ₜ[F.obj i.1] y) = (B.map (homOfLE h)).hom x * τ₀ j y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
               IsLocalization U (B.obj j))) ∧
          (letI := (B.map (homOfLE h)).hom.toAlgebra
           ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
             ∀ (y : B.obj j) (x : D.obj i),
               e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
        (∀ i : {i : I // i₀ ≤ i},
          letI := (τ₀ i).toAlgebra
          letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
          (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
            (∀ (x : B.obj i) (y : c.pt),
              φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T)) ∧
          (letI := (κ i).toAlgebra
           ∃ e : T ⊗[B.obj i] D.obj i ≃ₗ[T] N,
             ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x))
```

### Old wrapper (exists_limit_module_module_data, verbatim signature from the delivery base)

```lean
theorem exists_limit_module_module_data
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (N : AddCommGrpCat.{max u v}) [Module T N] (s t : ℕ)
    (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N))
    {i₀ : I} {B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}}
    {β : B ⟶ (Functor.const _).obj T}
    (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T)
    (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i)
    (hκ : ∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x)
    (hτ : ∀ i, IsLocalHom (τ₀ i))
    (hτe : ∀ i, (τ₀ i).EssFiniteType)
    (hcomp : ∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom)
    (hnat : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      (B.map (homOfLE h)).hom.comp (τ₀ i) = (τ₀ j).comp (F.map (homOfLE h)).hom) :
    ∃ (D : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{max u v})
        (δ : D ⟶ (Functor.const _).obj N),
      Nonempty (IsColimit (Cocone.mk N δ)) ∧
      ∃ (ν : ∀ i : {i : I // i₀ ≤ i}, D.obj i →+ N)
        (_ : ∀ i : {i : I // i₀ ≤ i}, Module (B.obj i) (D.obj i)),
        (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
        (∀ i, ∀ (y : B.obj i) (x : D.obj i), ν i (y • x) = κ i y • ν i x) ∧
        (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j)
          (y : B.obj i) (x : D.obj i),
          (D.map (homOfLE h)).hom (y • x) =
            (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
        (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
        (∀ i, ∃ H₀ : (Fin s → B.obj i) →ₗ[B.obj i] (Fin t → B.obj i),
          Nonempty (((Fin t → B.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B.obj i] D.obj i)) ∧
        (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
          letI := (τ₀ i).toAlgebra
          letI := (F.map (homOfLE h)).hom.toAlgebra
          (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
            (∀ (x : B.obj i) (y : F.obj j.1),
              φ (x ⊗ₜ[F.obj i.1] y) = (B.map (homOfLE h)).hom x * τ₀ j y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
               IsLocalization U (B.obj j))) ∧
          (letI := (B.map (homOfLE h)).hom.toAlgebra
           ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
             ∀ (y : B.obj j) (x : D.obj i),
               e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
        (∀ i : {i : I // i₀ ≤ i},
          letI := (τ₀ i).toAlgebra
          letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
          (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
            (∀ (x : B.obj i) (y : c.pt),
              φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T)) ∧
          (letI := (κ i).toAlgebra
           ∃ e : T ⊗[B.obj i] D.obj i ≃ₗ[T] N,
             ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x))
```

## New

The declarations RingHom.exists_limit_module_module_data_core and
RingHom.exists_limit_module_module_data are removed. Their DAG Lean records point to
RingHom.exists_limit_module_essentially_finite_presentation_over_system in
Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem, which realizes
joint descent once. No new copy of the joint statement is introduced.

The existing joint theorem has exactly its original signature. Its proof now obtains
localized ring data, obtains presented module data on a later tail, proves the tail
inclusion final, transports the ring colimit, and assembles restricted ring predicates
with module tensor equivalences. It imports LimitModuleLocalizationRingData,
LimitModuleModuleDataConstruction and Mathlib.CategoryTheory.Filtered.Final in place
of the removed proof dependency LimitModuleModuleData.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.LimitModuleModuleData | F2 | retire false core and wrapper; retain proved colimit-only theorem |
| Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem | unclaimed | forced proof/import adaptation; unchanged signature and visibility |

All other transitive importers use the unchanged joint theorem. No target or
definition changes. The two corrected helper nodes now realize the existing joint
theorem, rather than introducing duplicate Lean declarations.

## Forced adaptations

The original downstream proof uses exists_limit_module_module_data, which no longer
exists. Replacing its proof and proof imports is necessary to retain its unchanged
statement. The assembly formerly in the duplicate core is moved here verbatim.
The counterfactual compiler error and exact changes are in report.md and are checked
again by deliver3.py.

## Status

landed 20261014T020509-L-3810807 2026-10-14 (merge of deliver/F2/Sheaf.RingTheory.LimitModuleModuleData)
