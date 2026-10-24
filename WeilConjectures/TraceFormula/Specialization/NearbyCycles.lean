/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.SpecialFibre
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances
public import WeilConjectures.TraceFormula.KunnethVerdier

/-!

# Nearby cycles of the deformation of a contracting correspondence

Let `c = (c₁, c₂) : C ⟶ X × X` be contracting at the `k`-point `y` of its support, with
`x = c₁(y) = c₂(y)`, and let `k'` be a separably closed extension of `k`. The deformations to the
normal cones of `x ∈ X` and `y ∈ C`, base changed to the strictly henselian trait `Spec k'⟦t⟧`, are
models of `X` and `C` of finite type over the trait; so are the product model of `X × X` and the
model of the fixed locus. Their nearby cycles `Ψ = i^* Rj_* ε^*` restrict to the bounded
constructible derived categories by Deligne's finiteness theorem
(`ProEtale.CondensedRing.NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`).

This file defines
* the specialization functors `Ψ_X`, `Ψ_C`, `Ψ_{X×X}`, `Ψ_F`
  (`ProEtale.CondensedRing.specialization`, `ProEtale.CondensedRing.specializationProd`,
  `ProEtale.CondensedRing.Correspondence.IsContractingAt.specializationFixedLocus`);
* the *specialized correspondence* `c' = (γ₁, γ₂) : N_y C ⊗ k' ⟶ N_x X ⊗ k'` of
  `(N_x X ⊗ k', Ψ_X K)`
  (`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialCorrespondence`) and its fixed
  locus
  (`ProEtale.CondensedRing.Correspondence.IsContractingAt.specialFixedLocus`);

and states the two theorems on nearby cycles that Varshavsky's vanishing argument uses:
* Gabber's Künneth formula and the commutation of nearby cycles with Verdier duality, in the form
  `Ψ_{X×X}(K ⊠ D K) ≅ Ψ_X K ⊠ D Ψ_X K`
  (`ProEtale.CondensedRing.nonempty_specializationProd_externalProduct_iso`);
* Verdier's zero-section theorem: the specialization `Sp_{X,x}(K) = Ψ_X K` restricted to the zero
  section vanishes if `K_x` does
  (`ProEtale.CondensedRing.isZero_upperStar_zeroSection_specialization`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- Compatibility required from the nearby-cycles section (blueprint
`det-sp-nearby-cycles-exchanges`, to be proved there): **Deligne's finiteness theorem for nearby
cycles** (SGA 4½, [Th. finitude], Thm. 3.2; for `ℚ̄_ℓ`-coefficients
by passage to the limit, Bhatt–Scholze §6.8): over the strictly henselian trait
`Spec k'⟦t⟧`, `k'` separably closed, the nearby cycles of a model of finite type preserve bounded
constructible complexes. The pullback `ε^*` to the geometric generic fibre preserves them, and
`ī^* Rj̄_*` does by Deligne's theorem. -/
theorem NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel {X : Scheme.{u}}
    {X' : Over (Spec (.of k'))} (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) :=
  sorry


variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

section ZeroSection

variable (k') (x : RationalPoint X)

/-- The *specialization* `Sp_{X,x} : Dᵇc(X) ⥤ Dᵇc(N_x X ⊗ k')` to the normal cone of a rational
point `x` (Verdier, *Spécialisation de faisceaux et monodromie modérée*): the nearby cycles of the
deformation to the normal cone of `x`, base changed to the trait `Spec k'⟦t⟧`. -/
noncomputable def specialization :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((deformationSpecialFibre X x.left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k'))

/-- **Verdier's zero-section theorem** (Verdier, *Spécialisation de faisceaux et monodromie
modérée*, Prop. 8.(5); blueprint `det-sp-zero-section-vanishing`, `sk-thm-tf-sp-zero-section`):
the restriction of the specialization `Sp_{X,x}(K)` to the zero section `x ⊗ k'` of the normal
cone is the base change of the stalk `K_x`; in particular it vanishes if `K_x` does. -/
theorem isZero_upperStar_zeroSection_specialization
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (deformationSpecialFibreZeroSection X x.left.ker k')).obj
        ((specialization k' x).obj K)) :=
  sorry

/-- The specialization `Dᵇc(X × X) ⥤ Dᵇc((N_x X ⊗ k') × (N_x X ⊗ k'))` of the product: the nearby
cycles of the product over the trait of two copies of the deformation to the normal cone of
`x`. -/
noncomputable def specializationProd :
    Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((deformationSpecialFibre X x.left.ker k' ⨯
        deformationSpecialFibre X x.left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k'))

/-- **Nearby cycles of the universal kernel** (Gabber's Künneth formula for nearby cycles, Illusie,
*Autour du théorème de monodromie locale*, Thm. 4.7, blueprint `sk-prop-tf-nearby-external-kunneth`,
and Gabber's commutation of nearby cycles with Verdier duality, Illusie, loc. cit., Thm. 4.2,
blueprint `sk-prop-tf-nearby-duality-foundation`): the specialization of the universal kernel
`K ⊠ D K` is the universal kernel of the specialization,
`Ψ_{X×X}(K ⊠ D_X K) ≅ Ψ_X K ⊠ ΨX D_X K ≅ Ψ_X K ⊠ D Ψ_X K`. -/
theorem nonempty_specializationProd_externalProduct_iso
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((specializationProd k' x).obj (externalProduct ℓ K (verdierDual ℓ (toPoint X) K)) ≅
      externalProduct ℓ ((specialization k' x).obj K)
        (verdierDual ℓ (toPoint (deformationSpecialFibre X x.left.ker k'))
          ((specialization k' x).obj K))) :=
  sorry

end ZeroSection

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y)

namespace IsContractingAt

variable (k')

/-- The *specialized correspondence* `c' = (γ₁, γ₂) : N_y C ⊗ k' ⟶ N_x X ⊗ k'` of the
specialization `Ψ_X K` of `K` to the normal cone of `x = c₁(y)`: the special fibre of the
deformation of `c` to the normal cones (blueprint `det-tf-contracting-vanishing`). Its coefficient
map plays no role in the vanishing argument and is taken to be zero. -/
noncomputable def specialCorrespondence :
    Correspondence ℓ ((specialization k' (y ≫ c.c₁)).obj K) where
  C := deformationSpecialFibre c.C y.left.ker k'
  c₁ := hc.specialLeg₁ k'
  c₂ := hc.specialLeg₂ k'
  u := 0

/-- The fixed locus of the specialized correspondence, the fibre product `C' ×_{X' × X'} X'`. -/
noncomputable def specialFixedLocus : (hc.specialCorrespondence k').FixedLocus where
  F := fixedLocusOfDiag (hc.specialLeg₁ k') (hc.specialLeg₂ k')
  ι := fixedLocusOfDiag.ι _ _
  w := fixedLocusOfDiag.w _ _
  isLimit := fixedLocusOfDiag.isLimit _ _

/-- The specialization `Ψ_F` of the fixed locus `F`: the nearby cycles of the fibre product over
the trait of the deformed support `𝒞 ⟶ 𝒳 ×_S 𝒳` with the diagonal of `𝒳`, whose special fibre is
the fixed locus of the specialized correspondence. -/
noncomputable def specializationFixedLocus (F : c.FixedLocus) :
    Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((hc.specialFixedLocus k').F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    ((deformationFixedLocusModel k' c.c₁ c.c₂ hc.ker_map_le_c₁ hc.ker_map_le_c₂
      F.isPullback).preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationFixedLocusModel k' c.c₁ c.c₂ _ _ F.isPullback))

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
