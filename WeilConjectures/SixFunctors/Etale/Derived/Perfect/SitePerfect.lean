/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

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

/-- Dualizability of an étale sheaf, with the monoidal structure of a general coefficient
category (compare `AlgebraicGeometry.Etale.DerivedCategory.IsDualizableEtale`). -/
abbrev IsDualizableSheaf (F : Sheaf Y.smallEtaleTopology A) : Prop :=
  IsDualizable F

/-- A bounded complex of dualizable sheaves is dualizable in `D(Y_ét)`
(`DerivedCategory.isDualizable_Q_obj`). -/
theorem DerivedCategory.isDualizableEtale_Q_obj
    (P : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ n, IsDualizableSheaf (P.X n)) :
    DerivedCategory.IsDualizableEtale (_root_.DerivedCategory.Q.obj P) :=
  _root_.DerivedCategory.isDualizable_Q_obj P a b hP

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma IsDualizableSheaf.of_retract {F G : Sheaf Y.smallEtaleTopology A} (h : Retract F G)
    (hG : IsDualizableSheaf G) : IsDualizableSheaf F :=
  IsDualizable.of_retract h hG

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma IsDualizableSheaf.of_iso {F G : Sheaf Y.smallEtaleTopology A} (e : F ≅ G)
    (hF : IsDualizableSheaf F) : IsDualizableSheaf G :=
  IsDualizable.of_iso e hF

omit [Abelian.HasFunctorialFlatResolution A] in
lemma IsDualizableSheaf.biprod {F G : Sheaf Y.smallEtaleTopology A} (hF : IsDualizableSheaf F)
    (hG : IsDualizableSheaf G) : IsDualizableSheaf (F ⊞ G) :=
  IsDualizable.biprod hF hG

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma isDualizableSheaf_of_isZero {F : Sheaf Y.smallEtaleTopology A} (hF : IsZero F) :
    IsDualizableSheaf F :=
  CategoryTheory.IsZero.isDualizable hF

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
lemma isDualizableSheaf_unit : IsDualizableSheaf (𝟙_ (Sheaf Y.smallEtaleTopology A)) :=
  isDualizable_unit

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

/-- The constant sheaf `(Λ^m)_U` is dualizable: it is a finite biproduct of copies of the unit
sheaf `Λ_U` (`CategoryTheory.IsDualizable.biprod`). -/
theorem isDualizableSheaf_constantSheaf_pi {U : Scheme.{u}} (m : ℕ) :
    IsDualizableSheaf ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (Fin m → Λ))) := by
  have := (constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0}
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  induction m with
  | zero =>
    exact isDualizableSheaf_of_isZero (Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _))
  | succ m ih =>
    let e : ModuleCat.of Λ (Fin (m + 1) → Λ) ≅
        ModuleCat.of Λ Λ ⊞ ModuleCat.of Λ (Fin m → Λ) :=
      (Fin.consLinearEquiv Λ (fun _ : Fin (m + 1) ↦ Λ)).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of Λ Λ) (ModuleCat.of Λ (Fin m → Λ))).symm
    refine IsDualizableSheaf.of_iso ((constantSheaf _ _).mapIso e ≪≫
      Functor.mapBiprod (constantSheaf _ _) _ _).symm ?_
    exact IsDualizableSheaf.biprod isDualizableSheaf_unit ih

/-- An object of `D(U_ét, Λ)` isomorphic to a bounded complex of finite projective `Λ_U`-modules
is dualizable (`CategoryTheory.IsDualizable.of_retract`,
`AlgebraicGeometry.Etale.isDualizableSheaf_constantSheaf_pi`). -/
theorem isDualizableEtale_of_trivialization {U : Scheme.{u}}
    {M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ)))))
    (e : M ≅ DerivedCategory.Q.obj P) : DerivedCategory.IsDualizableEtale M :=
  (DerivedCategory.isDualizableEtale_Q_obj P a b fun n ↦
    have h := hP n
    IsDualizableSheaf.of_retract h.choose_spec.some
      (isDualizableSheaf_constantSheaf_pi h.choose)).of_iso e.symm

section Projection

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

/-- The derived adjunction `D(u_!) ⊣ Lu^*` for an étale morphism `u`, with the right adjoint
the left derived functor `Lu^*` (isomorphic to the levelwise `D(u^*)`, `u^*` being exact). -/
noncomputable def derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction {U : Scheme.{u}}
    (f : U ⟶ X) [Etale f] :
    (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory ⊣ L((f)^*[A]) :=
  let _ : CatCommSq ((Etale.etaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh
      (Etale.etaleLowerShriek A f inferInstance).mapDerivedCategory :=
    ⟨(Etale.etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.symm⟩
  let _ : CatCommSq (((f)^*[A]).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh L((f)^*[A]) :=
    ⟨(asIso ((f)^*[A]).leftDerivedFunctorCounit).symm⟩
  ((Etale.etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomotopyCategory
    (.up ℤ)).localization DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ _

/-- **Derived projection formula for an étale morphism** `u : U ⟶ X`: the projection map
`D(u_!)(Lu^*K ⊗ᴸ T) ⟶ K ⊗ᴸ D(u_!)T` of the adjunction `D(u_!) ⊣ Lu^*`, for the monoidal
structure `leftDerivedUpperStarMonoidal` of `Lu^*`, is an isomorphism. -/
theorem isIso_projectionMap_derivedEtaleLowerShriek {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    [(f)^*[A].PreservesFlat] (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A f
    IsIso (Functor.Monoidal.projectionMap
      (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K) :=
  sorry

/-- For étale `u` and `K` with `Lu^*K` dualizable, `Lu^*` sends the comparison
`RHom(K, 𝟙) ⊗ᴸ K ⟶ RHom(K, K)` to an isomorphism. By
`CategoryTheory.Functor.Monoidal.isIso_map_ihomUnitTensorToIhom`, this follows from the derived
projection formula `isIso_projectionMap_derivedEtaleLowerShriek`. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale_general
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f] [(f)^*[A].PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK : DerivedCategory.IsDualizableEtale ((L((f)^*[A])).obj K)) :
    IsIso ((L((f)^*[A])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) := by
  let := leftDerivedUpperStarMonoidal A f
  have := isIso_projectionMap_derivedEtaleLowerShriek (A := A) f K
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := Etale.DerivedCategory.nonempty_exactPairing_swap ((L((f)^*[A])).obj K)
    ((L((f)^*[A])).obj K)ᘁ
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom ((L((f)^*[A])).obj K)ᘁ ((L((f)^*[A])).obj K)
    ((L((f)^*[A])).obj K)
  exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K K

end Projection

/-- For an étale morphism `u : U ⟶ X` and `K` whose derived pullback `Lu^*K` is dualizable, the
derived pullback of the comparison `RHom(K, Λ_X) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism: for
étale `u` the derived pullback commutes with the internal hom, and the comparison for the
dualizable `Lu^*K` is an isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.IsDualizableEtale ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((L((f)^*[ModuleCat.{u + 1} Λ])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) :=
  isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale_general f K _hK

/-- On a member `u : U ⟶ X` of an étale cover on which `K` is isomorphic to a bounded complex of
finite projective `Λ_U`-modules, the derived pullback of the comparison
`RHom(K, Λ_X) ⊗ᴸ K ⟶ RHom(K, K)` is an isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_trivialization
    {U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ n, ∃ m : ℕ, Nonempty (Retract (P.X n)
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ)))))
    (e : (L((f)^*[ModuleCat.{u + 1} Λ])).obj K ≅ DerivedCategory.Q.obj P) :
    IsIso ((L((f)^*[ModuleCat.{u + 1} Λ])).map (DerivedCategory.ihomUnitTensorToIhomEtale K)) :=
  isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhomEtale_of_isDualizableEtale f K
    (isDualizableEtale_of_trivialization P a b ha hb hP e)

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
