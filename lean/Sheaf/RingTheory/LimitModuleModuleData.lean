module
public import Sheaf.RingTheory.LimitModuleRingData
@[expose] public section
universe u v p
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom
/-- Module-theoretic continuation of the finite presentation descent.
Source: Stacks Project, Algebra, Tags 00QX and 00R1.
(blueprint: lem-weil-pbc-limit-module-essentially-finite-presentation-over-system-module).

Proof: Descend the finite presentation matrix to a common stage, define the stage modules
as cokernels, and use right exactness of tensor products and the elementwise colimit
criterion to verify base change and the abelian-group colimit. -/
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
             ∀ (y : T) (x : D.obj i), e (y ⊗ₜ[B.obj i] x) = y • ν i x)) := by
  sorry
end RingHom
