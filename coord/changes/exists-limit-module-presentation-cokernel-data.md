# RingHom.exists_limit_module_presentation_cokernel_data

## Reason

Returned reviewer X-6a253 E2 exhibits the false fixed-tail conclusion: for k→T=k[x]_(x),
H=x and N=T/(x), no finite-dimensional k-module at 0 can base change to N.
G1/E2 separately shows that constant base F=k and B=(k→T) need not satisfy localization
base change even when N=0. Thus choose a later matrix stage, and move the exact ring
localization predicates to named hypotheses. The existing joint theorem obtains these predicates
from a new polynomial-quotient/localization construction, not as extra public assumptions.

## Old

This theorem is absent from the actual delivery base; it is a new construction obligation.
The returned, unlanded version existentially chose D on the entire supplied fixed tail
I≥i₀ and claimed both ring-localization predicates as conclusions. That false version
is replaced, not retained as a library interface. The review return records
the rejected interface and its two counterexamples.

## New

```lean
theorem exists_limit_module_presentation_cokernel_data
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (N : AddCommGrpCat.{max u v}) [Module T N]
    (s t : ℕ) (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N))
    (i₀ : I) (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
    (β : B ⟶ (Functor.const _).obj T)
    (hβcol : Nonempty (IsColimit (Cocone.mk T β)))
    (hBlocal : ∀ i : {i : I // i₀ ≤ i}, IsLocalRing (B.obj i))
    (hβlocal : ∀ i : {i : I // i₀ ≤ i}, IsLocalHom (β.app i).hom)
    (hBmaplocal : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      IsLocalHom (B.map (homOfLE h)).hom)
    (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T)
    (hκ : ∀ i x, κ i x = (β.app i).hom x)
    (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i)
    (hτlocal : ∀ i, IsLocalHom (τ₀ i))
    (hτfinite : ∀ i, (τ₀ i).EssFiniteType)
    (hτcomp : ∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom)
    (hτnat : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      (B.map (homOfLE h)).hom.comp (τ₀ i) =
        (τ₀ j).comp (F.map (homOfLE h)).hom)
    (hRingTrans : ∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
      letI := (τ₀ i).toAlgebra
      letI := (F.map (homOfLE h)).hom.toAlgebra
      (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
        (∀ (x : B.obj i) (y : F.obj j.1),
          φ (x ⊗ₜ[F.obj i.1] y) =
            (B.map (homOfLE h)).hom x * τ₀ j y) ∧
        (letI := φ.toAlgebra
         ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
           IsLocalization U (B.obj j))))
    (hRingLimit : ∀ i : {i : I // i₀ ≤ i},
      letI := (τ₀ i).toAlgebra
      letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
      (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
        (∀ (x : B.obj i) (y : c.pt),
          φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
        (letI := φ.toAlgebra
         ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T))) :
  ∃ (i₁ : I) (hi : i₀ ≤ i₁),
  let ρ : {i : I // i₁ ≤ i} ⥤ {i : I // i₀ ≤ i} :=
    { obj := fun i ↦ ⟨i.1, hi.trans i.2⟩
      map := fun h ↦ homOfLE (leOfHom h) }
  let B₁ := ρ ⋙ B
  let κ₁ : ∀ i : {i : I // i₁ ≤ i}, B₁.obj i →+* T := fun i ↦ κ (ρ.obj i)
  ∃ (D : {i : I // i₁ ≤ i} ⥤ AddCommGrpCat.{max u v}) (δ : D ⟶ (Functor.const _).obj N),
  Nonempty (IsColimit (Cocone.mk N δ)) ∧
  ∃ (ν : ∀ i : {i : I // i₁ ≤ i}, D.obj i →+ N)
    (_ : ∀ i : {i : I // i₁ ≤ i}, Module (B₁.obj i) (D.obj i)),
    (∀ i, ∀ x : D.obj i, ν i x = (δ.app i).hom x) ∧
    (∀ i, ∀ (y : B₁.obj i) (x : D.obj i), ν i (y • x) = κ₁ i y • ν i x) ∧
    (∀ (i j : {i : I // i₁ ≤ i}) (h : i ≤ j)
      (y : B₁.obj i) (x : D.obj i),
      (D.map (homOfLE h)).hom (y • x) =
        (B₁.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
    (∀ i, Module.Finite (B₁.obj i) (D.obj i)) ∧
    (∀ i, ∃ H₀ : (Fin s → B₁.obj i) →ₗ[B₁.obj i] (Fin t → B₁.obj i),
      Nonempty (((Fin t → B₁.obj i) ⧸ LinearMap.range H₀) ≃ₗ[B₁.obj i] D.obj i)) ∧
    (∀ (i j : {i : I // i₁ ≤ i}) (h : i ≤ j),
      (letI := (B₁.map (homOfLE h)).hom.toAlgebra
       ∃ e : B₁.obj j ⊗[B₁.obj i] D.obj i ≃ₗ[B₁.obj j] D.obj j,
         ∀ (y : B₁.obj j) (x : D.obj i),
           e (y ⊗ₜ[B₁.obj i] x) = y • (D.map (homOfLE h)).hom x)) ∧
    (∀ i : {i : I // i₁ ≤ i},
      (letI := (κ₁ i).toAlgebra
       ∃ e : T ⊗[B₁.obj i] D.obj i ≃ₗ[T] N,
         ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B₁.obj i] x) = y • ν i x))
```

The separate ring-only construction is RingHom.exists_limit_module_localization_ring_data,
node lem-limit-module-localization-ring-data. It descends a finite polynomial quotient and
localizes at contracted primes, giving the ring predicates independently of N, s, t, H.
The existing joint theorem restricts its witnesses along the existential tail inclusion and proves
that the restricted cocone is still a ring colimit by Mathlib's final-functor equivalence.
No ring-core interface outside the held module is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem | unclaimed | passes localization witnesses; restricts B, β, κ and τ₀ and packages module clauses at i₁ |

## Status

landed 20261014T020509-L-3810807 2026-10-14 (merge of deliver/F2/Sheaf.RingTheory.LimitModuleModuleData)
