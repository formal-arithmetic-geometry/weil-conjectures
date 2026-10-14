/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module
public import Sheaf.RingTheory.LimitModuleRingData
/-!
# Cokernels of a descended matrix on a later tail
Source: Stacks Project, Algebra, Tag 00QX (the choice of λ₂), and Tag 00R1.
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data)
-/

@[expose] public section
universe u v p
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom


/-- Presentation-cokernel module data after restricting a descended ring diagram.
Source: Stacks Project, Algebra, Tag 00QX, presentation-matrix paragraph; Tag 00R1.
Proof:
1. Express H using the standard bases as its finite t-by-s matrix. The ring colimit
   represents each entry at some stage of B. Directedness supplies a common stage
   i₁ ≥ i₀ for all entries. For an empty matrix take i₁ = i₀. Restrict B, β, κ and
   τ₀ to the tail above i₁. That tail is cofinal: every old index has a common upper
   bound with i₁. Hence its ring colimit is still T, and both ring-localization
   hypotheses restrict to it. They are hypotheses, not consequences of colimitness.
2. Map the lifted matrix at i₁ into each later ring B₁(i), obtaining Hᵢ. Define
   D(i) as the additive group of the actual quotient B₁(i)^t / range Hᵢ (lifted
   to universe max u v). Ring transitions send matrix columns to matrix columns,
   so entrywise maps descend to semilinear quotient maps. Composition and identity
   follow on representatives. The presentation equivalence at T identifies the
   limit quotient with N and induces δ and ν. Their naturality and scalar formulas
   also follow on representatives. The t standard basis classes generate D(i).
3. Tensoring a cokernel is right exact. Base change carries the finite free modules
   and the lifted matrix to the later free modules and matrices. Thus it identifies
   B₁(j) ⊗[B₁(i)] D(i) with D(j) and T ⊗[B₁(i)] D(i) with N. On pure tensors the
   maps are precisely multiplication by the scalar followed by the quotient map.
4. A vector representing an element of N has finitely many coordinates, so it
   lifts to a common stage. If a stage vector maps to zero in N, it is H applied
   to a finite vector over T. Lift that vector's coordinates to a later stage;
   the finitely many equalities with the original vector hold at a still later
   stage by the eventual-equality criterion for the ring colimit. Consequently
   the quotient class is zero there. For any additive cocone define its map from
   N by a representative. Two choices become equal at a common later stage by
   applying the zero criterion to their difference. This gives a well-defined
   additive map, factoring each leg, and representatives prove uniqueness.
   Therefore the displayed additive cocone has colimit N on the chosen later tail.
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module-data) -/
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
         ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B₁.obj i] x) = y • ν i x)) := by
  sorry
end RingHom
