/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# Derived extension of scalars along a quotient map and the internal hom

Let `φ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel `(a)`,
for instance `Λ ⟶ Λ ⧸ (ϖⁿ)`, and let `X` be a scheme. The extension of scalars of étale sheaves
`Λ' ⊗_Λ -` is a strong monoidal left adjoint of restriction of scalars which preserves flat
objects; its total left derived functor `K ↦ K ⊗ᴸ_Λ Λ'`
(`AlgebraicGeometry.Etale.derivedExtendScalars`) is therefore left adjoint to the derived
restriction of scalars and monoidal. We deduce:

- `AlgebraicGeometry.Etale.isDerivedBaseChange_derivedExtendScalarsAdjunction_unit`: the unit
  `K ⟶ Res(K ⊗ᴸ Λ')` exhibits `K ⊗ᴸ Λ'` as the derived base change of `K`;
- `AlgebraicGeometry.Etale.derivedHomRestrictScalarsIso`: the extension–restriction adjunction
  for internal homs, `RHom_Λ(K, Res N) ≅ Res RHom_{Λ'}(K ⊗ᴸ Λ', N)`;
- `AlgebraicGeometry.Etale.nonempty_iso_derivedRestrictScalars_derivedExtendScalars`: with
  scalars restricted back to `Λ`, `K ⊗ᴸ_Λ Λ'` is the derived tensor product of `K` with the
  constant sheaf `Λ ⧸ (a)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

include hφ ha in
/-- Extension of scalars of étale sheaves along a surjective ring morphism with principal kernel
sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms: with scalars restricted
back, it is tensoring with a constant sheaf. -/
lemma preservesKFlatQuasiIso_extendScalars :
    (Sheaf.extendScalars X.smallEtaleTopology φ).PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ :=
    have := Sheaf.reflectsIsomorphisms_restrictScalars X.smallEtaleTopology hφ
    CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (Sheaf.extendScalarsCompRestrictScalarsIso X.smallEtaleTopology hφ ha) f hK hL

/-- The derived extension of scalars `K ↦ K ⊗ᴸ_Λ Λ'`, from `D(X_ét, Λ)` to `D(X_ét, Λ')`, along
a surjective ring morphism `φ : Λ →+* Λ'` with principal kernel: the total left derived functor
of the extension of scalars of étale sheaves. -/
noncomputable def derivedExtendScalars : 𝐃(X, Λ) ⥤ 𝐃(X, Λ') :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  (Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedFunctor

/-- The derived extension of scalars is left adjoint to the derived restriction of scalars. -/
noncomputable def derivedExtendScalarsAdjunction :
    derivedExtendScalars hφ ha X ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars X.smallEtaleTopology φ).rightDerivedFunctorIsoMapDerivedCategory

/-- The unit `K ⟶ Res(K ⊗ᴸ_Λ Λ')` exhibits `K ⊗ᴸ_Λ Λ'` as the derived base change of `K`. -/
lemma isDerivedBaseChange_derivedExtendScalarsAdjunction_unit (K : 𝐃(X, Λ)) :
    Sheaf.IsDerivedBaseChange ((derivedExtendScalarsAdjunction hφ ha X).unit.app K) :=
  fun N ↦ by
    convert ((derivedExtendScalarsAdjunction hφ ha X).homEquiv K N).bijective using 1
    ext g
    exact ((derivedExtendScalarsAdjunction hφ ha X).homEquiv_unit K N g).symm

/-- Any derived base change of `K` along `φ` is isomorphic to `K ⊗ᴸ_Λ Λ'`. -/
lemma nonempty_iso_derivedExtendScalars_of_isDerivedBaseChange {K : 𝐃(X, Λ)} {K' : 𝐃(X, Λ')}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty ((derivedExtendScalars hφ ha X).obj K ≅ K') := by
  let adj := derivedExtendScalarsAdjunction hφ ha X
  have := Sheaf.IsDerivedBaseChange.isIso
    (isDerivedBaseChange_derivedExtendScalarsAdjunction_unit hφ ha X K) hη
    ((adj.homEquiv K K').symm η) (by rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply])
  exact ⟨asIso ((adj.homEquiv K K').symm η)⟩

/-- The derived extension of scalars is monoidal: `(K ⊗ᴸ M) ⊗ᴸ_Λ Λ' ≅ (K ⊗ᴸ_Λ Λ') ⊗ᴸ (M ⊗ᴸ_Λ Λ')`,
naturally in `M`. -/
noncomputable def derivedExtendScalarsTensorIso (K : 𝐃(X, Λ)) :
    (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K ⋙ derivedExtendScalars hφ ha X ≅
      derivedExtendScalars hφ ha X ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ') X).obj ((derivedExtendScalars hφ ha X).obj K) :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  have := Sheaf.preservesFlat_extendScalars X.smallEtaleTopology hφ ha
  (asIso (Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedTensorComparisonOfKFlat).app K

/-- The extension–restriction adjunction for internal homs:
`RHom_Λ(K, Res N) ≅ Res RHom_{Λ'}(K ⊗ᴸ_Λ Λ', N)`, naturally in `N`. Both sides are right
adjoint to `M ↦ (K ⊗ᴸ M) ⊗ᴸ_Λ Λ' ≅ (K ⊗ᴸ_Λ Λ') ⊗ᴸ (M ⊗ᴸ_Λ Λ')`. -/
noncomputable def derivedHomRestrictScalarsIso (K : 𝐃(X, Λ)) :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙
        (derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K) ≅
      (derivedHom (ModuleCat.{u + 1} Λ') X).obj (op ((derivedExtendScalars hφ ha X).obj K)) ⋙
        Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
  conjugateIsoEquiv
    ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).comp
      (derivedExtendScalarsAdjunction hφ ha X))
    ((derivedExtendScalarsAdjunction hφ ha X).comp
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ') ((derivedExtendScalars hφ ha X).obj K)))
    (derivedExtendScalarsTensorIso hφ ha X K).symm

/-- With scalars restricted back to `Λ`, the derived extension of scalars `K ⊗ᴸ_Λ Λ'` is the
derived tensor product `K ⊗ᴸ (Λ ⧸ (a))_X` with the constant sheaf: on a K-flat complex `P`
both are computed by the complex `P ⊗ (Λ ⧸ (a))_X`. -/
lemma nonempty_iso_derivedRestrictScalars_derivedExtendScalars (L : 𝐃(X, Λ)) :
    Nonempty ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj
        ((derivedExtendScalars hφ ha X).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ RingHom.ker φ))))) := by
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  let F := Sheaf.extendScalars X.smallEtaleTopology φ
  let R := Sheaf.restrictScalars X.smallEtaleTopology φ
  let c := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (Λ ⧸ RingHom.ker φ))
  obtain ⟨P, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso L
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P').1 hP
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P' hP'
  have := _root_.DerivedCategory.isIso_tensorLeftCounit _ hP
  let S := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj c
  refine ⟨R.mapDerivedCategory.mapIso ((derivedExtendScalars hφ ha X).mapIso e.symm) ≪≫
    R.mapDerivedCategory.mapIso
      (asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P'))) ≪≫
    R.mapDerivedCategory.mapIso
      (_root_.DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors _).app P') ≪≫
        (_root_.DerivedCategory.quotientCompQhIso _).app _) ≪≫
    R.mapDerivedCategoryFactors.app _ ≪≫
    _root_.DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
          (Sheaf.extendScalarsCompRestrictScalarsIso X.smallEtaleTopology hφ ha) _).app P' ≪≫
        ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _) c).app
          P').symm) ≪≫
    ((_root_.DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    _root_.DerivedCategory.Qh.mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) P' S).symm ≪≫
    (asIso ((_root_.DerivedCategory.tensorLeftCounit _).app _)).symm ≪≫
    tensorIso e ((_root_.DerivedCategory.quotientCompQhIso _).app S ≪≫
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app c).symm)⟩

end Etale

end AlgebraicGeometry
