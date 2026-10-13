module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.AffinePushoutRingAffineSections
import Mathlib.Algebra.Category.Ring.Constructions
set_option linter.style.longLine false
set_option linter.style.whitespace false
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" =>
  (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology U)).homEquiv A U.sheaf).symm (𝟙 A)
/-- Ring section presentation needed for the affine pushout argument.

Source: Stacks Project, Morphisms, Tag 01SB, affine pushout section calculation.
(blueprint: lem-weil-pbc-affine-pushout-ring-section-presentation).

Proof: identify sections on the affine inverse image with the tensor product of the
 two affine section rings using the pushout universal property.  The second tensor
 inclusion gives `δ`; the counit triangle gives `ε (δ c) = c`, and pure tensors
 generate the tensor product, yielding the displayed finite-sum formula.  This
 calculation is valid for zero rings and empty affine opens as well. -/
theorem affine_pushout_ring_section_presentation [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u})
    (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    ∃ δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)),
      (∀ c, (ε.hom.app (op (f ⁻¹ᵁ V))).hom (δ c) = c) ∧
      (∀ r : B.obj.obj (op (f ⁻¹ᵁ V)),
        ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)),
          r = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 * δ x.2).sum) := by
  classical
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology U)
  let δ : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)) :=
    (t.hom.app (op (f ⁻¹ᵁ V))).hom.comp ((adj.unit.app A).hom.app (op V)).hom
  refine ⟨δ, ?_, ?_⟩
  · intro c
    have ht := congrArg (fun q ↦ q.hom.app (op (f ⁻¹ᵁ V)) (
      (adj.unit.app A).hom.app (op V) c)) hring.2.2
    have hu := (adj.homEquiv A U.sheaf).apply_symm_apply (𝟙 A)
    rw [Adjunction.homEquiv_unit] at hu
    have hv := congrArg (fun q ↦ q.hom.app (op V) c) hu
    exact ht.trans hv
  · let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    have hs := affine_pushout_ring_affine_sections f B b t hring.1 V hV
    let ht := CommRingCat.isPushout_tensorProduct
      Γ(X, V) Γ(U, f ⁻¹ᵁ V) Γ(U, f ⁻¹ᵁ V)
    let e := (ht.isoIsPushout _ _ hs).commRingCatIsoToRingEquiv
    have hl (c : Γ(U, f ⁻¹ᵁ V)) :
        e (c ⊗ₜ[Γ(X, V)] 1) = (b.hom.app (op (f ⁻¹ᵁ V))).hom c := by
      exact congrArg (fun q ↦ q.hom c) (IsPushout.inl_isoIsPushout_hom _ _ ht hs)
    have hr (d : Γ(U, f ⁻¹ᵁ V)) : e (1 ⊗ₜ[Γ(X, V)] d) = δ d := by
      exact congrArg (fun q ↦ q.hom d) (IsPushout.inr_isoIsPushout_hom _ _ ht hs)
    have htmul (c d : Γ(U, f ⁻¹ᵁ V)) :
        e (c ⊗ₜ[Γ(X, V)] d) = (b.hom.app (op (f ⁻¹ᵁ V))).hom c * δ d := by
      rw [← hl c, ← hr d, ← map_mul]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    intro r
    obtain ⟨x, rfl⟩ := e.surjective r
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul c d => exact ⟨[(c, d)], by simpa using htmul c d⟩
    | add x y hx hy =>
      obtain ⟨l, hl⟩ := hx
      obtain ⟨m, hm⟩ := hy
      exact ⟨l ++ m, by simp [map_add, hl, hm]⟩
end
end AlgebraicGeometry.Scheme.Modules
