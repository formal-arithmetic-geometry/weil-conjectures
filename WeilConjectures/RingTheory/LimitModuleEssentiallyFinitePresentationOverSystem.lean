/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.LimitModuleLocalizationRingData
import WeilConjectures.RingTheory.LimitModuleModuleDataConstruction
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Descent of a local algebra and a presented module along a given local-ring system

Given a directed system of local rings with colimit `A`, a localization `T = B_q` of a finitely
presented `A`-algebra and a finitely presented `T`-module descend to compatible systems of local
algebras and finite modules over a tail of the system.

## Implementation details

The finitely many coefficients of `B = A[x₁, …, xₙ]/(f₁, …, fₘ)` descend to a common stage, and
the stage algebras are localized at the inverse-image primes, so all maps are local. Polynomial
extension and quotient base change identify the scalar extensions, and filtered-colimit criteria
show that the colimit is `T`. The module is the cokernel of a `t × s` matrix whose entries also
descend; right exactness of the tensor product identifies the scalar extensions of the stage
cokernels, and an elementwise criterion over `ℤ` proves the abelian-group colimit assertion.

## References

* [Stacks, Tags 00QV, 00QX, 00R1]
-/

@[expose] public section

universe u v p

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- Descend a localization of a finitely presented algebra and a finite module presentation
along the given directed system. Scalar-extension maps are specified on pure tensors; the
module tensors put the new scalar ring first, using tensor symmetry to match the source.
-/
theorem exists_limit_module_essentially_finite_presentation_over_system
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T)
    (N : AddCommGrpCat.{max u v}) [Module T N]
    (s t : ℕ) (H : (Fin s → T) →ₗ[T] (Fin t → T))
    (hN : Nonempty (((Fin t → T) ⧸ LinearMap.range H) ≃ₗ[T] N)) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T),
          (∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧ (∀ i, IsLocalHom (κ i)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) ∧
          ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
            (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
            (∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              (B.map (homOfLE h)).hom.comp (τ₀ i) =
                (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
            ∃ (D : {i : I // i₀ ≤ i} ⥤ AddCommGrpCat.{max u v}) (δ : D ⟶ (Functor.const _).obj N),
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
                      φ (x ⊗ₜ[F.obj i.1] y) =
                        (B.map (homOfLE h)).hom x * τ₀ j y) ∧
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
                     ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x)) := by
  obtain ⟨i₀, B, β, hcol, κ, hκ, hBlocal, hκlocal, hBmap, τ₀, hτlocal,
      hτfinite, hτcomp, hτnat, hRingTrans, hRingLimit⟩ :=
    exists_limit_module_localization_ring_data F c hc hF hcLocal T τ P W f hf hT
  have hβlocal : ∀ i, IsLocalHom (β.app i).hom := by
    intro i
    have heq : κ i = (β.app i).hom := by ext x; exact hκ i x
    rw [← heq]
    exact hκlocal i
  obtain ⟨i₁, hi, D, δ, hDcol, ν, hModule, hν, hνsmul, hmap, hfinite,
      hpres, htrans, hlimit⟩ :=
    exists_limit_module_presentation_cokernel_data F c hc hF hcLocal T τ N s t H hN
      i₀ B β hcol hBlocal hβlocal hBmap κ hκ τ₀ hτlocal hτfinite hτcomp hτnat
      hRingTrans hRingLimit
  let ρ : {i : I // i₁ ≤ i} ⥤ {i : I // i₀ ≤ i} :=
    { obj := fun i ↦ ⟨i.1, hi.trans i.2⟩
      map := fun h ↦ homOfLE (leOfHom h) }
  let B₁ := ρ ⋙ B
  let β₁ : B₁ ⟶ (Functor.const _).obj T := Functor.whiskerLeft ρ β
  let κ₁ : ∀ i : {i : I // i₁ ≤ i}, B₁.obj i →+* T := fun i ↦ κ (ρ.obj i)
  let τ₁ := fun i ↦ τ₀ (ρ.obj i)
  let : Nonempty {i : I // i₁ ≤ i} := ⟨⟨i₁, le_rfl⟩⟩
  let : IsDirected {i : I // i₁ ≤ i} (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩⟩
  let : ρ.Final := by
    refine Functor.final_of_exists_of_isFiltered ρ ?_ ?_
    · intro i
      obtain ⟨k, hik, h₁k⟩ := exists_ge_ge i.1 i₁
      exact ⟨⟨k, h₁k⟩, ⟨homOfLE hik⟩⟩
    · intro i j f g
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  have hcol₁ : Nonempty (IsColimit (Cocone.mk T β₁)) :=
    ⟨(Functor.Final.isColimitWhiskerEquiv ρ (Cocone.mk T β)).symm hcol.some⟩
  refine ⟨i₁, B₁, β₁, hcol₁, κ₁, ?_, ?_, ?_, ?_, τ₁, ?_, ?_, ?_, ?_,
    D, δ, hDcol, ν, hModule, hν, hνsmul, hmap, hfinite, hpres, ?_, ?_⟩
  · intro i x
    exact hκ (ρ.obj i) x
  · intro i
    exact hBlocal (ρ.obj i)
  · intro i
    exact hκlocal (ρ.obj i)
  · intro i j h
    exact hBmap (ρ.obj i) (ρ.obj j) h
  · intro i
    exact hτlocal (ρ.obj i)
  · intro i
    exact hτfinite (ρ.obj i)
  · intro i
    exact hτcomp (ρ.obj i)
  · intro i j h
    exact hτnat (ρ.obj i) (ρ.obj j) h
  · intro i j h
    exact ⟨hRingTrans (ρ.obj i) (ρ.obj j) h, htrans i j h⟩
  · intro i
    exact ⟨hRingLimit (ρ.obj i), hlimit i⟩

end RingHom
