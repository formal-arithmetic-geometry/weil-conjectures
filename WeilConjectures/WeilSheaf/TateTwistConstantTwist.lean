/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DerivedHom

/-!
# The Tate twist of Weil complexes is a derived constant twist

The Tate sheaf `ℚ̄_ℓ(m)` is the constant Weil twist `ℚ̄_ℓ ⊗ 𝓑_b` of `ℚ̄_ℓ` by `b = χ_ℓ(σ)ᵐ`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafObjIso`), and internal homs out of `ℚ̄_ℓ ⊗ 𝓑_c` are
constant twists by `c⁻¹`. Hence the Tate twist `K ↦ K(m) = R[ℚ̄_ℓ(m)^∨, K]` of Weil complexes is,
in the derived category of pro-étale Weil sheaves, the levelwise constant twist by `b`, the
constant twist being exact.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorConstantTwistAdicConstantIso`:
  `[ℚ̄_ℓ ⊗ 𝓑_b, -] ≅ (-) ⊗ 𝓑_{b⁻¹}`.
- `AlgebraicGeometry.WeilComplex.tateTwistCompιIso`: the Tate twist `(-)(m)` followed by the
  inclusion into the derived category is the derived constant twist by `χ_ℓ(σ)ᵐ`.
- `AlgebraicGeometry.WeilComplex.tateTwistObjAdicConstantIso`: `ℚ̄_ℓ(m)` as a Weil complex is
  the constant twist of `ℚ̄_ℓ` by `χ_ℓ(σ)ᵐ`, placed in degree `0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor Opposite

namespace AlgebraicGeometry

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

namespace ProEtaleWeilSheaf

/-- The internal hom out of the constant twist `ℚ̄_ℓ ⊗ 𝓑_b` of `ℚ̄_ℓ` is the constant twist by
`b⁻¹`: `[ℚ̄_ℓ ⊗ 𝓑_b, B] ≅ B ⊗ 𝓑_{b⁻¹}`, naturally in `B`. On underlying sheaves it is the
canonical isomorphism `𝓗om(ℚ̄_ℓ, B) ≅ B`. -/
noncomputable def ihomFunctorConstantTwistAdicConstantIso (b : (PadicAlgCl l)ˣ) :
    ihomFunctor k₀ l X ((constantTwist k₀ l X b).obj (adicConstant k₀ l X)) ≅
      constantTwist k₀ l X b⁻¹ :=
  NatIso.ofComponents (fun B ↦ ihomConstantTwistLeftIso _ B b ≪≫
      (constantTwist k₀ l X b⁻¹).mapIso (ihomAdicConstantIso B)) fun f ↦
    IsoAlgebra.hom_ext ((Category.id_comp _).trans
      ((Mod.ihomRegularIso.hom.naturality f.hom.f).trans (Category.id_comp _).symm))

end ProEtaleWeilSheaf

namespace WeilComplex

/-- **The Tate twist is a derived constant twist.** The Tate twist `(-)(m)` of Weil complexes,
followed by the inclusion into the derived category of pro-étale Weil sheaves, is the derived
functor of the exact constant twist by `χ_ℓ(σ)ᵐ`: `ℚ̄_ℓ(m)^∨ ≅ ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)⁻ᵐ}` and internal
homs out of `ℚ̄_ℓ ⊗ 𝓑_c` are constant twists by `c⁻¹`. -/
noncomputable def tateTwistCompιIso (m : ℤ) :
    tateTwist k₀ l X m ⋙ (objectProperty k₀ l X).ι ≅
      (objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.constantTwist k₀ l X
          (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _
      (objectProperty_rightDerivedFunctor_ihomFunctor _
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m).dual) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorNatIso
          ((ProEtaleWeilSheaf.ihomBifunctor k₀ l X).mapIso
            (WeilSheaf.dualObjIsoOfIso _ (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m)
              (WeilSheaf.tateTwistSheafObjIso k₀ l X m)).symm.op ≪≫
            ProEtaleWeilSheaf.ihomFunctorConstantTwistAdicConstantIso k₀ l X
              (WeilSheaf.cyclotomicUnit k₀ l ^ m)⁻¹ ≪≫
            eqToIso (by rw [inv_inv])) ≪≫
        Functor.rightDerivedFunctorIsoMapDerivedCategory _)

/-- The Tate sheaf `ℚ̄_ℓ(m)`, as the Tate twist of the Weil complex `ℚ̄_ℓ`, is the constant twist
`ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}` placed in degree `0`. -/
noncomputable def tateTwistObjAdicConstantIso (m : ℤ) :
    ((tateTwist k₀ l X m).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))).obj ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).obj
          (ProEtaleWeilSheaf.adicConstant k₀ l X)) :=
  (tateTwistCompιIso k₀ l X m).app _ ≪≫
    ((ProEtaleWeilSheaf.constantTwist k₀ l X
      (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategorySingleFunctor 0).app
        (ProEtaleWeilSheaf.adicConstant k₀ l X)

end WeilComplex

end AlgebraicGeometry
