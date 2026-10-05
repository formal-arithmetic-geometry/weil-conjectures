/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.WeilSheaf.Dual

/-!
# Tensor products and constant twists of Weil sheaves

The tensor product `F ⊗ G` of two Weil sheaves is the tensor product of the underlying étale
sheaves on the geometric fiber `X̄`, with the Weil structure

`Fr^* (F ⊗ G) ≅ Fr^* F ⊗ Fr^* G ≅ F ⊗ G`

given by the monoidal structure of the pullback `Fr^*` and the two Weil structures.

For a unit `b ∈ ℚ̄_ℓˣ` the *constant Weil twist* `F ⊗ 𝓑_b` of `F` is the tensor product of `F`
with the geometrically constant Weil line `𝓑_b` on which the geometric Frobenius acts by `b`.
Since `𝓑_b` is the unit sheaf with its Weil structure multiplied by `b`, the twist is the same
étale sheaf as `F`, with its Weil structure `φ` replaced by `b • φ`; this is how it is defined
here. At a point with values in `𝔽_{qᵐ}` the local Frobenius of the twist is `bᵐ` times the
local Frobenius of `F`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.tensorObj`: the tensor product `F ⊗ G` of two Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.constantTwist`: the constant Weil twist `F ⊗ 𝓑_b`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilCoefficients

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- Multiplication by a unit `b` of `ℚ̄_ℓ`, as an automorphism of a sheaf of `ℚ̄_ℓ`-modules. -/
noncomputable def smulIso (b : (PadicAlgCl l)ˣ) (M : Sheaf J (WeilCoefficients.{u} l)) :
    M ≅ M where
  hom := ObjectProperty.homMk (ULift.up (b : PadicAlgCl l) • 𝟙 M.obj)
  inv := ObjectProperty.homMk (ULift.up ((b⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) • 𝟙 M.obj)
  hom_inv_id := by
    ext1
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
      ObjectProperty.FullSubcategory.id_hom]
    exact (congrArg (· • 𝟙 M.obj) (congrArg ULift.up (Units.inv_mul b))).trans (one_smul _ _)
  inv_hom_id := by
    ext1
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
      ObjectProperty.FullSubcategory.id_hom]
    exact (congrArg (· • 𝟙 M.obj) (congrArg ULift.up (Units.mul_inv b))).trans (one_smul _ _)

end WeilCoefficients

namespace WeilSheaf

-- TODO: prove once the category is redefined (`sk-d-real-operations`)
/-- The tensor product of the underlying sheaves of two Weil sheaves is constructible: tensor
products of constructible sheaves are constructible. -/
theorem isConstructibleSheaf_tensorObj (F G : WeilSheaf k₀ l X) :
    Scheme.IsConstructibleSheaf (F.obj.carrier ⊗ G.obj.carrier) :=
  sorry

/-- The tensor product `F ⊗ G` of two Weil sheaves: the tensor product of the underlying étale
sheaves on `X̄`, with the Weil structure

`Fr^* (F ⊗ G) ≅ Fr^* F ⊗ Fr^* G --φ_F ⊗ φ_G--> F ⊗ G`

built from the monoidal structure `CategoryTheory.Functor.Monoidal.μIso` of the pullback
`Fr^*` and the two Weil structures. -/
noncomputable def tensorObj (F G : WeilSheaf k₀ l X) : WeilSheaf k₀ l X where
  obj := .mk (F.obj.carrier ⊗ G.obj.carrier)
    ((Functor.Monoidal.μIso (frobeniusPullback k₀ l X) _ _).symm ≪≫
      (F.obj.str ⊗ᵢ G.obj.str))
  property := isConstructibleSheaf_tensorObj F G

/-- The constant Weil twist `F ⊗ 𝓑_b` of a Weil sheaf by a unit `b ∈ ℚ̄_ℓˣ`: the tensor product
of `F` with the geometrically constant Weil line `𝓑_b` on which the geometric Frobenius acts
by `b`. It is the étale sheaf of `F` with the Weil structure `b • φ`, so that at a point with
values in `𝔽_{qᵐ}` its local Frobenius is `bᵐ` times that of `F`, and every eigenvalue `α` of
the local Frobenius of `F` at a closed point of degree `m` becomes `bᵐ α`.
(blueprint: `def-wf-constant-weil-twist`) -/
noncomputable def constantTwist (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l X where
  obj := .mk F.obj.carrier (F.obj.str ≪≫ WeilCoefficients.smulIso b F.obj.carrier)
  property := F.property

/-- A constant twist of a lisse Weil sheaf is lisse, the underlying étale sheaf being the same. -/
theorem IsLisse.constantTwist {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (b : (PadicAlgCl l)ˣ) :
    (F.constantTwist b).IsLisse :=
  hF

end WeilSheaf

end AlgebraicGeometry
