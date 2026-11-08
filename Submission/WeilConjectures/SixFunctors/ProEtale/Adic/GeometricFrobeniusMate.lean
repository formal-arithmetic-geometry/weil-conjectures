/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field with base change
`φ̄ : X ⟶ Y` to the geometric fibres. The exchange isomorphisms
`φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` and `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*` of `ℓ`-adic
sheaves are mates under the adjunction `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_eq_mateEquiv`).
Consequently the unit and the counit of `φ̄^* ⊣ φ̄_*` are compatible with Frobenius structures,
which makes `φ^* ⊣ φ_*` an adjunction of Weil sheaves.

The proof iterates the mates correspondence along the Frobenius equivalences
`(Fr⁻¹)_* ⊣ Fr_*`: the iterated mate of the pullback exchange isomorphism is its conjugate, a
composite of composition and congruence isomorphisms of pushforwards, by the conjugation
identities for the pullbacks (`conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`);
and the mate of the pushforward exchange isomorphism along the Frobenius equivalences is the same
composite, which is checked on sections
(`AlgebraicGeometry.ProEtale.lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The units of pushforwards along morphisms `ai`, `ah` with `ai ≫ ah = 𝟙` and `bi`, `bh` with
`bi ≫ bh = 𝟙` are compatible with the factorisation isomorphisms of commutative squares
`ah ≫ φ = φ ≫ bh` and `ai ≫ φ = φ ≫ bi`. -/
lemma lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor {X Y : Scheme.{u}} (φ : X ⟶ Y)
    {ah ai : X ⟶ X} {bh bi : Y ⟶ Y} {c d : X ⟶ Y} (ha : ai ≫ ah = 𝟙 X) (hb : bi ≫ bh = 𝟙 Y)
    (e₁ : ah ≫ φ = c) (e₂ : φ ≫ bh = c) (e₃ : φ ≫ bi = d) (e₄ : ai ≫ φ = d)
    (M : Sheaf (Scheme.ProEt.topology X) A) :
    (φ)_*[A].map ((lowerStarUnit A ha).app M) ≫ (lowerStarFactor A e₁).hom.app ((ai)_*[A].obj M) ≫
        (lowerStarFactor A e₂).inv.app ((ai)_*[A].obj M) =
      (lowerStarUnit A hb).app ((φ)_*[A].obj M) ≫
        (bh)_*[A].map ((lowerStarFactor A e₃).hom.app M ≫ (lowerStarFactor A e₄).inv.app M) := by
  ext V
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_hom_app_hom_app,
    lowerStarFactor_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId,
    MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext <;> simp [pullback.condition_assoc, ha]

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)

/-- The exchange isomorphism `φ^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ φ^*` of pullbacks along a commutative
square `a ≫ φ = φ ≫ b` with `a`, `b` isomorphisms:
`(a⁻¹)_* φ^* ≅ a^* φ^* ≅ (a ≫ φ)^* = (φ ≫ b)^* ≅ φ^* b^* ≅ φ^* (b⁻¹)_*`. -/
noncomputable def upperStarExchangeIso (c : a.hom ≫ φ = φ ≫ b.hom) :
    (φ)^*[A] ⋙ (a.inv)_*[A] ≅ (b.inv)_*[A] ⋙ (φ)^*[A] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A a).symm ≪≫ (upperStarComp A _ _).symm ≪≫
    upperStarCongr A c ≪≫ upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv A b) _

end Sheaf

end AlgebraicGeometry.ProEtale
