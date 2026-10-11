/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Descent of a local algebra and a presented module along a given local-ring system

Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system).
-/

universe u v p

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- Descend a localization of a finitely presented algebra and a finite module presentation
along the given directed system. Scalar-extension maps are specified on pure tensors; the
module tensors put the new scalar ring first, using tensor symmetry to match the source.

Source: Stacks Project, Algebra, Tags 00QV, 00QX and 00R1
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system).

Proof:
1. Write `T = B_q`, where `B = A[x₁,...,xₙ]/(f₁,...,fₘ)`. The prime contracts to the
   maximal ideal of `A`. Descend the finitely many coefficients to a common stage and
   localize the resulting algebras at the inverse-image primes. Their contraction to
   each base stage is maximal, so all structure and transition maps are local.
   Use [lem-weil-pbc-localization-of-localization] and
   [lem-weil-pbc-filtered-colimit-algebras-elementwise].
2. Polynomial extension and quotient base change identify the scalar extensions of
   these presentations. Their colimit is `B`: lift finite coefficient sets to a stage;
   relations vanishing in `B` vanish at a later stage after descending their finite
   witnesses. Localizing at the compatible primes gives colimit `T`. The tail is cofinal.
   Use [lem-weil-pbc-polynomial-scalar-extension], [lem-weil-pbc-tensor-quotient-base-change],
   [lem-weil-pbc-filtered-colimit-rings-zero],
   [lem-weil-pbc-filtered-colimit-localization-at-prime],
   [lem-weil-pbc-colimit-initial-full-subcategory] and
   [lem-weil-pbc-filtered-colimit-modules-criterion].
3. Base change of localization gives an intermediate localization of the polynomial
   quotient at each later stage, then localization at the inverse-image prime gives
   the local stage ring. The same argument applies at the limit. Use
   [lem-weil-pbc-localization-base-change], [lem-weil-pbc-localization-of-localization]
   and [lem-weil-pbc-tensor-quotient-base-change].
4. Descend the finitely many entries of the given `t × s` presentation matrix to one
   common later stage. Define each stage module as its cokernel, with the induced
   compatible semilinear transition maps and maps to `N`. These modules are finite.
   Use [lem-weil-pbc-filtered-colimit-algebras-elementwise] and
   [def-weil-finitely-generated-module].
5. Tensoring these presentations is right exact and carries each matrix to the later
   matrix, so the canonical scalar-extension maps are module isomorphisms, including
   at the limit. Use [lem-weil-pbc-tensor-right-exact] and
   [lem-weil-pbc-module-base-change-universal-property].
6. Every module element is represented by a finite vector and lifts to a common stage.
   A vector becoming zero is a combination of finitely many matrix columns. Descend
   its coefficients and then its coordinate equalities to a later stage. The
   elementwise colimit criterion over `ℤ` proves the abelian-group colimit assertion.
   Use [lem-weil-pbc-filtered-colimit-algebras-elementwise],
   [lem-weil-pbc-filtered-colimit-rings-zero] and
   [lem-weil-pbc-filtered-colimit-modules-criterion].
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
  sorry

end RingHom
