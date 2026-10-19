module
public import WeilConjectures.RingTheory.LimitModuleRingData
@[expose] public section
universe u v p
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom
/-- The tail subtype has a least object at the chosen base index.
Source: elementary order theory.
Proof: pair the base index with reflexivity; every tail element has the defining
inequality from the base index.
(blueprint: lem-limit-module-tail-least) -/
theorem limit_module_tail_has_least
    {I : Type u} [Preorder I] {i₀ : I} :
    ∃ j₀ : {i : I // i₀ ≤ i}, ∀ j, j₀ ≤ j := by
  exact ⟨⟨i₀, le_refl i₀⟩, fun j => j.property⟩
/-- The directed-system module construction has a colimit part.
Source: Stacks Project, Algebra, Tag 00QX.
Proof: Take the constant diagram at N with its identity cocone. The tail has the least
object i₀. A cocone out of this diagram is determined by its component at i₀: naturality
along i₀ ≤ j identifies every component with it. This proves the colimit universal property.
(blueprint: lem-limit-module-colimit-part) -/
theorem exists_limit_module_module_data_colimit_part
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
      Nonempty (IsColimit (Cocone.mk N δ)) := by
  have _ := hc
  have _ := hF
  have _ := hcLocal
  have _ := hN
  have _ := hκ
  have _ := hτ
  have _ := hτe
  have _ := hcomp
  have _ := hnat
  let J := {i : I // i₀ ≤ i}
  obtain ⟨j₀, hj₀⟩ := limit_module_tail_has_least (I := I) (i₀ := i₀)
  refine ⟨(Functor.const J).obj N, 𝟙 _, ⟨?_⟩⟩
  refine { desc := fun q => q.ι.app j₀, fac := ?_, uniq := ?_ }
  · intro q j
    simpa using (q.w (homOfLE (show j₀ ≤ j from hj₀ j))).symm
  · intro q m hm
    simpa using hm j₀

end RingHom
