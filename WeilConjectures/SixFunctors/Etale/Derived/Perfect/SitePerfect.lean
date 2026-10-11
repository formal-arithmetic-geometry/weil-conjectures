/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Perfect complexes on the coefficient site

A complex `K` of étale sheaves of `Λ`-modules on `X` is *perfect on the coefficient site*
(blueprint `def-weil-site-perfect-complex`) if, on the members `U ⟶ X` of some étale cover,
its restriction `K|_U` is isomorphic to a bounded complex of finite projective `Λ_U`-modules,
a finite projective module being a direct summand of a finite sum `Λ_U^{⊕m}` of copies of the
constant sheaf.

## Implementation notes

The blueprint works on the small pro-étale site; the definition is stated here on the small
étale site of the étale model of the coefficient categories, the restriction to `U` being the
derived pullback `Lu^*` along the member `u : U ⟶ X` of the cover. A direct summand of
`Λ_U^{⊕m}` is a retract of the constant sheaf with value `Λ^m`. The coefficient ring is
arbitrary: for `Λ = A_{E,n}` this is the finite stage of the blueprint, and for `Λ = 𝒪_E` it
is the integral stage in the étale model. Elsewhere in the repository perfectness is rendered as
dualizability for the derived tensor product
(`WeilConjectures.SixFunctors.Etale.Derived.Perfect`).

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect`: perfectness on the coefficient site.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Blueprint `def-weil-site-perfect-complex`: Perfect complexes on the coefficient site.

An object `K` of `D(X_ét, Λ)` is *perfect on the coefficient site* if there is an étale cover
`{uᵢ : Uᵢ ⟶ X}` such that each restriction `Luᵢ^* K` is isomorphic to (the image in
`D(Uᵢ, Λ)` of) a bounded complex `P` of sheaves of `Λ`-modules on `Uᵢ` whose terms are finite
projective, i.e. retracts of the constant sheaf `(Λ^m)_{Uᵢ}` for some `m`. -/
def DerivedCategory.IsSitePerfect
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ (P : CochainComplex (Sheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
        ((constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin m → Λ))))) ∧
      Nonempty ((L((𝒰.f i)^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj P)

/-- Perfectness on the coefficient site is invariant under isomorphism. -/
lemma DerivedCategory.IsSitePerfect.of_iso
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (e : K ≅ K')
    (hK : DerivedCategory.IsSitePerfect K) : DerivedCategory.IsSitePerfect K' := by
  obtain ⟨𝒰, h⟩ := hK
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨e'⟩⟩ := h i
  exact ⟨P, a, b, ha, hb, hP, ⟨(L((𝒰.f i)^*[ModuleCat.{u + 1} Λ])).mapIso e.symm ≪≫ e'⟩⟩

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- For a dualizable `K`, the internal hom out of `K` commutes with tensoring by any `T`:
`RHom(K, M ⊗ᴸ T) ≅ RHom(K, M) ⊗ᴸ T`, both sides being `K^∨ ⊗ᴸ M ⊗ᴸ T`
(`AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`). -/
theorem DerivedCategory.nonempty_iso_derivedHom_derivedTensor_of_isDualizable
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hK : IsDualizable K)
    (M T : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((RHom(Y)[A].obj (op K)).obj (((derivedTensor A Y).obj M).obj T) ≅
      ((derivedTensor A Y).obj ((RHom(Y)[A].obj (op K)).obj M)).obj T) := by
  obtain ⟨e₁⟩ := DerivedCategory.nonempty_iso_coefficientDual_tensor hK (M ⊗ T)
  obtain ⟨e₂⟩ := DerivedCategory.nonempty_iso_coefficientDual_tensor hK M
  exact ⟨e₁.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e₂ T⟩

end General

section Reduction

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- Dualizability in `D(Y_ét)`, with the monoidal structure of a general coefficient category.
Stated through this abbreviation, statements about `A = ModuleCat Λ` use the same monoidal
instance as the general results they are deduced from. -/
abbrev DerivedCategory.IsDualizableEtale (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Prop :=
  IsDualizable K

/-- The comparison `RHom(K, Λ_Y) ⊗ᴸ K ⟶ RHom(K, K)` in `D(Y_ét)`, for a general coefficient
category. -/
noncomputable abbrev DerivedCategory.ihomUnitTensorToIhomEtale
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (ihom K).obj (𝟙_ _) ⊗ K ⟶ (ihom K).obj K :=
  MonoidalClosed.ihomUnitTensorToIhom K K

/-- An object `K` of `D(Y_ét)` is dualizable as soon as the comparison
`RHom(K, Λ_Y) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism: `RHom(K, Λ_Y)` is then a left dual of `K`
(`CategoryTheory.MonoidalClosed.exactPairingOfIsIso`), hence also a right dual, the derived
tensor product being symmetric. -/
theorem DerivedCategory.isDualizable_of_isIso_ihomUnitTensorToIhom
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    [IsIso (MonoidalClosed.ihomUnitTensorToIhom K K)] : IsDualizable K := by
  let := MonoidalClosed.exactPairingOfIsIso K
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap ((ihom K).obj (𝟙_ _)) K
  exact ⟨⟨(ihom K).obj (𝟙_ _)⟩⟩

variable
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [instF : ∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [instC : ConcreteCategory.{u + 1} A FC]
  [instR : (CategoryTheory.forget A).ReflectsIsomorphisms]
  [instP : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [instS : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include instF instC instR instP instS

/-- **Restrictions to an étale cover jointly reflect isomorphisms in `D(Y_ét)`**: a morphism
whose derived pullbacks to the members of an étale cover are isomorphisms is an isomorphism,
since the pullbacks commute with the cohomology sheaves and restrictions of sheaves along a
jointly surjective family reflect isomorphisms
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`). -/
theorem DerivedCategory.isIso_of_isIso_leftDerivedUpperStar_map_of_cover
    (𝒰 : Cover.{u} etalePrecoverage Y) {M N : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (φ : M ⟶ N) (h : ∀ i, IsIso ((L((𝒰.f i)^*[A])).map φ)) : IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective A 𝒰.f
    (fun x ↦ ?_) _ fun i ↦ ?_
  · exact 𝒰.exists_eq x
  · have := h i
    exact (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso A (𝒰.f i) n) φ).2
      (inferInstanceAs (IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
        ((L((𝒰.f i)^*[A])).map φ))))

/-- An object of `D(Y_ét)` is dualizable if, on the members of some étale cover, the derived
pullback of the comparison `RHom(K, Λ_Y) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism. -/
theorem DerivedCategory.isDualizable_of_cover (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (h : ∀ i, IsIso ((L((𝒰.f i)^*[A])).map (DerivedCategory.ihomUnitTensorToIhomEtale K))) :
    DerivedCategory.IsDualizableEtale K :=
  have := DerivedCategory.isIso_of_isIso_leftDerivedUpperStar_map_of_cover 𝒰 _ h
  DerivedCategory.isDualizable_of_isIso_ihomUnitTensorToIhom K

end Reduction

/-- On a member `u : U ⟶ X` of an étale cover on which `K` is isomorphic to a bounded complex of
finite projective `Λ_U`-modules, the derived pullback of the comparison
`RHom(K, Λ_X) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ)))))
    (_e : (L((f)^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj P) :
    IsIso ((L((f)^*[ModuleCat.{u + 1} Λ])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) :=
  sorry

/-- A complex which is perfect on the coefficient site is dualizable for the derived tensor
product: dualizability can be checked on an étale cover
(`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_of_cover`), and on the members of a
trivializing cover the comparison map is an isomorphism
(`isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization`). -/
theorem DerivedCategory.IsSitePerfect.isDualizable
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.IsSitePerfect K) : DerivedCategory.IsDualizableEtale K := by
  obtain ⟨𝒰, h⟩ := hK
  refine DerivedCategory.isDualizable_of_cover K 𝒰 fun i ↦ ?_
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  exact isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization (𝒰.f i) K P a b
    ha hb hP e

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
internal hom between finite levels.

If the first variable `K` is perfect on the coefficient site, the internal hom commutes with
the reduction of the coefficients along `Λ ⟶ Λ/J`, for any ideal `J`:
`RHom(K, L) ⊗ᴸ (Λ/J)_X ≅ RHom(K, L ⊗ᴸ (Λ/J)_X)`. As in the blueprint, `K` being site-perfect,
its internal hom is a tensor product with its coefficient dual, which commutes with coefficient
change. -/
theorem nonempty_iso_reductionModIdeal_derivedHom_of_isSitePerfect (J : Ideal Λ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.IsSitePerfect K)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((reductionModIdeal Λ X J).obj
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj L) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((reductionModIdeal Λ X J).obj L)) := by
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_derivedHom_derivedTensor_of_isDualizable
    hK.isDualizable L ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))
  exact ⟨e.symm⟩

end Etale

end AlgebraicGeometry
