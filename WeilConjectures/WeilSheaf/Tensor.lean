/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.LowerShriek

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

- `AlgebraicGeometry.LAdicWeilSheaf.tensorObj`: the tensor product `F ⊗ G` of two Weil sheaves.
- `AlgebraicGeometry.LAdicWeilSheaf.constantTwist`: the constant Weil twist `F ⊗ 𝓑_b`.
- `AlgebraicGeometry.LAdicWeilSheaf.constantTwistInvIso`: twisting by `b` and then by `b⁻¹` gives
  back `F`.

## Main statements

- `AlgebraicGeometry.LAdicWeilSheaf.nonempty_higherLowerShriek_constantTwist_iso`: the projection
  formula `Rⁱf₀!(F ⊗ 𝓑_b) ≅ Rⁱf₀!F ⊗ 𝓑_b` for a constant twist
  (blueprint: `lem-wf-constant-twist-cohomology`).
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

namespace LAdicWeilSheaf

/-- The tensor product `F ⊗ G` of two Weil sheaves: the tensor product of the underlying étale
sheaves on `X̄`, with the Weil structure

`Fr^* (F ⊗ G) ≅ Fr^* F ⊗ Fr^* G --φ_F ⊗ φ_G--> F ⊗ G`

built from the monoidal structure `CategoryTheory.Functor.Monoidal.μIso` of the pullback
`Fr^*` and the two Weil structures. -/
noncomputable def tensorObj (F G : LAdicWeilSheaf k₀ l X) : LAdicWeilSheaf k₀ l X where
  obj := .mk (F.obj.carrier ⊗ G.obj.carrier)
    ((Functor.Monoidal.μIso (frobeniusPullback k₀ l X) _ _).symm ≪≫
      (F.obj.str ⊗ᵢ G.obj.str))
  -- with the present coefficients `F` is zero, hence so is `F ⊗ G`, and the zero sheaf is
  -- constructible
  property := (Etale.constructibleSheaf _ _).prop_of_isZero
    (isZero_tensorObj_of_isZero_left F.isZero_carrier _)

/-- The constant Weil twist `F ⊗ 𝓑_b` of a Weil sheaf by a unit `b ∈ ℚ̄_ℓˣ`: the tensor product
of `F` with the geometrically constant Weil line `𝓑_b` on which the geometric Frobenius acts
by `b`. It is the étale sheaf of `F` with the Weil structure `b • φ`, so that at a point with
values in `𝔽_{qᵐ}` its local Frobenius is `bᵐ` times that of `F`, and every eigenvalue `α` of
the local Frobenius of `F` at a closed point of degree `m` becomes `bᵐ α`.
(blueprint: `def-wf-constant-weil-twist`) -/
noncomputable def constantTwist (F : LAdicWeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    LAdicWeilSheaf k₀ l X where
  obj := .mk F.obj.carrier (F.obj.str ≪≫ WeilCoefficients.smulIso b F.obj.carrier)
  property := F.property

/-- A constant Weil twist of `F` is lisse exactly when `F` is: it has the same underlying étale
sheaf. -/
@[simp]
theorem isLisse_constantTwist {F : LAdicWeilSheaf k₀ l X} {b : (PadicAlgCl l)ˣ} :
    (F.constantTwist b).IsLisse ↔ F.IsLisse :=
  Iff.rfl

-- TODO(adic): the Weil structure of `F ⊗ 𝓑_b` is `b • φ`, so the iterated structure at a
-- point of degree `m` is `bᵐ • φ_m` (`AlgebraicGeometry.LAdicWeilSheaf.frobeniusPowIso`).
/-- At a closed point `x` of degree `m`, the stalk of the constant twist `F ⊗ 𝓑_b` is the stalk
of `F` with its local Frobenius multiplied by `bᵐ`. (blueprint: `def-wf-constant-weil-twist`) -/
theorem nonempty_equiv_stalk_constantTwist (F : LAdicWeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ)
    (x : X.finitePoints) :
    Nonempty (((F.constantTwist b).stalk x).Equiv ((F.stalk x).rescale
      ((b : PadicAlgCl l) ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))) := by
  sorry

/-- Twisting by `b` and then by `b⁻¹` gives back the Weil sheaf: both twists keep the
underlying étale sheaf, and the Weil structure `b⁻¹ • b • φ` is `φ`. -/
noncomputable def constantTwistInvIso (F : LAdicWeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    (F.constantTwist b).constantTwist b⁻¹ ≅ F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change _ ≫ F.obj.str.hom = ((F.obj.str ≪≫ WeilCoefficients.smulIso b F.obj.carrier) ≪≫
      WeilCoefficients.smulIso b⁻¹ F.obj.carrier).hom ≫ 𝟙 _
    have : (WeilCoefficients.smulIso b⁻¹ F.obj.carrier).hom =
        (WeilCoefficients.smulIso b F.obj.carrier).inv := rfl
    simp only [this, Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (congrArg (· ≫ _) ((frobeniusPullback k₀ l X).map_id _)).trans
      (Category.id_comp _))))

-- TODO(adic): needs the projection formula for `Rf₀!` and constant Weil sheaves
/-- The projection formula for a constant twist: for a morphism `f : X ⟶ Y` of `k₀`-schemes as
in `AlgebraicGeometry.LAdicWeilSheaf.higherLowerShriek` and a unit `b ∈ ℚ̄_ℓˣ`,
`Rⁱf₀!(F ⊗ 𝓑_b) ≅ Rⁱf₀!F ⊗ 𝓑_b`: the constant Weil line `𝓑_b` is pulled back from `Y`, so it
comes out of the direct image (blueprint: `lem-wf-constant-twist-cohomology`). -/
theorem nonempty_higherLowerShriek_constantTwist_iso {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (F : LAdicWeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) (i : ℕ) :
    Nonempty ((higherLowerShriek k₀ l f i).obj (F.constantTwist b) ≅
      ((higherLowerShriek k₀ l f i).obj F).constantTwist b) :=
  sorry

end LAdicWeilSheaf

end AlgebraicGeometry
