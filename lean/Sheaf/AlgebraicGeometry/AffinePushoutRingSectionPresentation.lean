module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
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
  sorry
end
end AlgebraicGeometry.Scheme.Modules
